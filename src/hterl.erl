-module(hterl).


-export([file/1, file/2]).

-export([report_error/1]).
-export([format_error/1]).

-define(DEFAULT_ENCODING, utf8).

-record(state, {
    infile,
    inport,
    outfile,
    forms = [],
    errors = [],
    warnings = [],
    options = []
}).

-type syntaxTree() :: erl_syntax:syntaxTree().
-type tags() :: {tags, term(), [tag()]}.
-type tag() :: {tag, term(), atom(), [tag_attr()], [syntaxTree()]}.
-type tag_attr() :: {attr, term(), atom(), syntaxTree()} | {min_attr, term(), atom()}.
-type opts() :: [option()].
-type option() :: term().
-type state() :: #state{}.

%%====================================================================
%% API functions
%%====================================================================

file(Path) ->
    file(Path, []).

-spec file(string(), opts()) -> ok | {ok, list()} | error | {error, list(), list()}.
file(Path, Options) ->
    St = start(Path, #state{options = Options}),
    infile(St).

%%====================================================================
%% Internal functions
%%====================================================================

start(InFileX, St) ->
    Output = get_option(output, St),
    InFile = assure_extension(InFileX, ".hterl"),
    OutFileX = filename:rootname(InFile, ".hterl"),
    OutFile = assure_extension(OutFileX, output_extension(Output)),
    St#state{
        infile = InFile,
        outfile = OutFile
    }.

output_extension(beam) -> ".beam";
output_extension(erl) -> ".erl".


infile(St0) ->
    InFile = St0#state.infile,
    St = case hterl_epp:open(InFile, []) of
        {ok, Epp} ->
            St1 = St0#state{inport = Epp},
            passes(St1);
        {error, Reason} ->
            add_error(InFile, none, {file_error, Reason}, St0)
    end,
    case has_errors(St) of
        true -> file:delete(St#state.outfile), ok;
        false -> ok
    end,
    hterl_ret(St).

has_errors(#state{errors = []}) -> false;
has_errors(_) -> true.

assure_extension(File, Ext) ->
    lists:concat([strip_extension(File, Ext), Ext]).

%% Assumes File is a filename.
strip_extension(File, Ext) ->
    case filename:extension(File) of
        Ext -> filename:rootname(File);
        _Other -> File
    end.

hterl_ret(St) ->
    report_errors(St),
    case St of
        #state{errors=[], warnings=[]} -> ok;
        #state{errors=[], warnings=Ws} -> {ok, Ws};
        #state{errors=Es, warnings=Ws} -> {error, Es, Ws}
    end.

passes(St) ->
    case get_option(output, St) of
        beam -> compile(transform(parse(St)));
        erl -> output(transform(parse(St)))
    end.


transform(St) ->
    {Forms, St1} = lists:mapfoldl(fun rewrite/2, St, St#state.forms),
    St1#state{forms = lists:map(fun erl_syntax:revert/1, Forms)}.

compile(St) ->
    #state{forms=Forms, outfile=OutFile} = St,
    case compile:forms(Forms, [return]) of
        {ok, _Mod, Bin} ->
            ok = file:write_file(OutFile, Bin),
            St;
        {ok, _Mod, Bin, Ws} ->
            ok = file:write_file(OutFile, Bin),
            St#state{warnings = Ws};
        {error, Es, Ws} ->
            St#state{errors = St#state.errors ++ Es, warnings = Ws}
    end.

output(St) ->
    #state{forms=Forms, outfile=OutFile} = St,
    FileOpts = [write, delayed_write, {encoding, utf8}],
    case file:open(OutFile, FileOpts) of
        {ok, OutPort} ->
            try
                [write_form(OutPort, Form) || Form <- Forms],
                St
            after
                file:close(OutPort)
            end;
        {error, Reason} ->
            add_error(OutFile, none, {file_error, Reason}, St)
    end.

write_form(Port, Form) ->
    PP = erl_pp:form(Form),
    ok = file:write(Port, [PP, $\n]).

report_errors(St) ->
    lists:foreach(fun report_error/1, lists:sort(St#state.errors)).

report_error({File, {none, Mod, E}}) ->
    io:fwrite(<<"~ts: ~ts\n">>, [File,Mod:format_error(E)]);
report_error({File, {Line, Mod, E}}) ->
    io:fwrite(<<"~ts:~w: ~ts\n">>, [File,Line,Mod:format_error(E)]).

parse(St0) ->
    St = parse_next(St0#state.inport, St0),
    St#state{forms = lists:reverse(St#state.forms)}.

parse_next(Inport, St0) ->
    Form = read_form(Inport),
    case parse(Form, St0) of
        {eof, St} -> St;
        St -> parse_next(Inport, St)
    end.

parse(eof, St) ->
    {eof, St};
parse({error, ErrorLine, Error}, St0) ->
    add_error(erl_anno:new(ErrorLine), Error, St0);
parse(Form, St0) ->
    St0#state{forms = [Form | St0#state.forms]}.

read_form(Epp) ->
    case hterl_epp:scan_hterl_form(Epp) of
        {ok, Toks} ->
            case hterl_parser:parse(Toks) of
                {error, {ErrorLine, Mod, Message}} ->
                    {error, ErrorLine, {error, Mod, Message}};
                {ok, Form} ->
                    Form
            end;
        {eof, _Line} ->
            eof
    end.

-spec rewrite(tags() | syntaxTree(), state()) -> {syntaxTree(), state()}.
rewrite({tags, _Anno, Tags}, St) ->
    case proplists:get_bool(precompile, St#state.options) of
        true -> rewrite_tags_pre(Tags, St);
        false -> rewrite_tags_ehtml(Tags, St)
    end;
rewrite(Tree, St) ->
    Fun = fun (T, StN) -> rewrite(T, StN) end,
    erl_syntax_lib:mapfold_subtrees(Fun, St, Tree).

-spec rewrite_tags_ehtml([tag()], state()) -> {syntaxTree(), state()}.
rewrite_tags_ehtml(Tags, St) ->
    {Tags1, St1} = lists:mapfoldl(fun rewrite_tag_ehtml/2, St, Tags),
    {list_unless_singleton(Tags1), St1}.

-spec rewrite_tag_ehtml(tag(), state()) -> {syntaxTree(), state()}.
rewrite_tag_ehtml({tag, _Anno, Name, [], []}, St) ->
    {erl_syntax:tuple([erl_syntax:atom(Name)]), St};
rewrite_tag_ehtml({tag, _Anno, Name, Attrs, []}, St) ->
    {Attrs1, St1} = rewrite_attrs_ehtml(Attrs, St),
    {erl_syntax:tuple([erl_syntax:atom(Name), Attrs1]), St1};
rewrite_tag_ehtml({tag, _Anno, Name, Attrs, Exprs}, St) ->
    {Attrs1, St1} = rewrite_attrs_ehtml(Attrs, St),
    {Exprs1, St2} = lists:mapfoldl(fun rewrite/2, St1, Exprs),
    Body = list_unless_singleton(Exprs1),
    {erl_syntax:tuple([erl_syntax:atom(Name), Attrs1, Body]), St2}.

-spec rewrite_attrs_ehtml([tag_attr()], state()) -> {syntaxTree(), state()}.
rewrite_attrs_ehtml(Attrs, St) ->
    {Attrs1, St1} = lists:mapfoldl(fun rewrite_attr_ehtml/2, St, Attrs),
    {erl_syntax:list(Attrs1), St1}.

-spec rewrite_attr_ehtml(tag_attr(), state()) ->  {syntaxTree(), state()}.
rewrite_attr_ehtml({min_attr, _Anno, Name}, St) ->
    {erl_syntax:atom(Name), St};
rewrite_attr_ehtml({attr, _Anno, Name, Expr}, St) ->
    {Expr1, St1} = rewrite(Expr, St),
    {erl_syntax:tuple([erl_syntax:atom(Name), Expr1]), St1}.

-spec rewrite_tags_pre([tag()], state()) -> {syntaxTree(), state()}.
rewrite_tags_pre(Tags, St) ->
    Encoding = get_option(encoding, St),
    {Tags1, St1} = lists:mapfoldl(fun rewrite_tag_pre/2, St, Tags),
    Result = erl_syntax:tuple([
        erl_syntax:atom(pre_html),
        compact(flatten(Tags1), Encoding)
    ]),
    % This annotation lets us distinguish a generated
    % pre_html tuple from one that was in the source.
    AnnotatedResult = erl_syntax:add_ann(prerendered, Result),
    {AnnotatedResult, St1}.

-spec rewrite_tag_pre(tag(), state()) -> {syntaxTree(), state()}.
rewrite_tag_pre({tag, _Anno, Name, Attrs, []}, St0) ->
    {Attrs1, St} = lists:mapfoldl(fun rewrite_attr_pre/2, St0, Attrs),
    Result = erl_syntax:list(
        [erl_syntax:string("<" ++ atom_to_list(Name))] ++
        Attrs1 ++
        [erl_syntax:string(html_end_tag(Name))]
    ),
    {Result, St};
rewrite_tag_pre({tag, _Anno, Name, Attrs, Body}, St0) ->
    {Attrs1, St1} = lists:mapfoldl(fun rewrite_attr_pre/2, St0, Attrs),
    {Body1, St} = lists:mapfoldl(fun interpolate_expr/2, St1, Body),
    Result = erl_syntax:list(
        [erl_syntax:string("<" ++ atom_to_list(Name))] ++
        Attrs1 ++
        [erl_syntax:string(">")] ++
        Body1 ++
        [erl_syntax:string("</" ++ atom_to_list(Name) ++ ">")]
    ),
    {Result, St}.

-spec rewrite_attr_pre(tag_attr(), state()) -> {syntaxTree(), state()}.
rewrite_attr_pre({min_attr, _Anno, Name}, St) ->
    {erl_syntax:string(" " ++ atom_to_list(Name)), St};
rewrite_attr_pre({attr, _Anno, Name, Expr0}, St0) ->
    {Expr, St} = interpolate_attr_expr(Expr0, St0),
    Result = erl_syntax:list([
        erl_syntax:string(" " ++ atom_to_list(Name) ++ "=\""),
        Expr,
        erl_syntax:string("\"")
    ]),
    {Result, St}.

-spec interpolate_expr(syntaxTree(), state()) -> {syntaxTree(), state()}.
interpolate_expr(SourceExpr, St0) ->
    Pos = erl_syntax:get_pos(SourceExpr),
    {Expr, St1} = rewrite(SourceExpr, St0),
    case erl_syntax:type(Expr) of
        string ->
            interpolate_string(erl_syntax:string_value(Expr), Pos, St1);
        char ->
            interpolate_string([erl_syntax:char_value(Expr)], Pos, St1);
        integer ->
            interpolate_string([erl_syntax:integer_value(Expr)], Pos, St1);
        nil ->
            {erl_syntax:nil(), St1};
        list ->
            Elems0 = erl_syntax:list_elements(Expr),
            {Elems, St} = lists:mapfoldl(fun interpolate_expr/2, St1, Elems0),
            {erl_syntax:list(Elems), St};
        list_comp ->
            {Template, St} = interpolate_expr(erl_syntax:list_comp_template(Expr), St1),
            Body = erl_syntax:list_comp_body(Expr),
            {erl_syntax:list_comp(Template, Body), St};
        tuple ->
            case has_ann(prerendered, Expr) of
                true ->
                    % This is a {pre_html, _} tuple that was generated from a tags expression.
                    % It's safe to extract the rendered blob and elide the call to `interpolate`.
                    [First, Second] = erl_syntax:tuple_elements(Expr),
                    true = erl_syntax:is_atom(First, pre_html),
                    {Second, St1};
                false ->
                    {apply_interpolate(Expr, St1), St1}
            end;
        _ ->
            {apply_interpolate(Expr, St1), St1}
    end.

-spec has_ann(term(), syntaxTree()) -> boolean().
has_ann(A, Node) ->
    lists:member(A, erl_syntax:get_ann(Node)).

-spec interpolate_attr_expr(syntaxTree(), state()) -> {syntaxTree(), state()}.
interpolate_attr_expr(SourceExpr, St0) ->
    Pos = erl_syntax:get_pos(SourceExpr),
    {Expr, St1} = rewrite(SourceExpr, St0),
    case erl_syntax:type(Expr) of
        string ->
            interpolate_string(erl_syntax:string_value(Expr), Pos, St1);
        char ->
            interpolate_string(integer_to_list(erl_syntax:char_value(Expr)), Pos, St1);
        integer ->
            interpolate_string(integer_to_list(erl_syntax:integer_value(Expr)), Pos, St1);
        _ ->
            {apply_interpolate_attr(Expr, St1), St1}
    end.

-spec interpolate_string(string(), term(), state()) -> {syntaxTree(), state()}.
interpolate_string(String, Pos, St0) ->
    Encoding = get_option(encoding, St0),
    {Sanitized, St} = case unicode:characters_to_list(String, Encoding) of
        {error, _, _} ->
            {"", add_error(Pos, {invalid_character, Encoding}, St0)};
        ValidString ->
           {hterl_api:htmlize(ValidString), St0}
    end,
    {erl_syntax:string(Sanitized), St}.

apply_interpolate_attr(Value, Opts) ->
    Encoding = get_option(encoding, Opts),
    erl_syntax:application(
        erl_syntax:atom(hterl_api),
        erl_syntax:atom(interpolate_attr),
        [Value, erl_syntax:abstract(Encoding)]).

apply_interpolate(Value, Opts) ->
    Encoding = get_option(encoding, Opts),
    erl_syntax:application(
        erl_syntax:atom(hterl_api),
        erl_syntax:atom(interpolate),
        [Value, erl_syntax:abstract(Encoding)]).

list_unless_singleton([Single]) -> Single;
list_unless_singleton(List) -> erl_syntax:list(List).

flatten(List) ->
    flatten_append(List, []).

flatten_append([], Tail) ->
    Tail;
flatten_append([H|T], Tail) ->
    case erl_syntax:is_list_skeleton(H) of
        true ->
            flatten_append(erl_syntax:list_elements(H), flatten_append(T, Tail));
        false ->
            [H] ++ flatten_append(T, Tail)
    end.

compact(List, Encoding) ->
    Elements = compact(List, [], [], Encoding),
    list_unless_singleton(lists:reverse(Elements)).

compact([], Fields, Elements, _Encoding) ->
    compact_fields(Fields, Elements);
compact([H|T], Fields, Elements, Encoding) ->
    case erl_syntax:type(H) of
        string ->
            {String, T1} = compact_strings([H|T]),
            compact(T1, [string_binary_field(String, Encoding) | Fields], Elements, Encoding);
        binary ->
            compact(T, lists:reverse(erl_syntax:binary_fields(H), Fields), Elements, Encoding);
        _ ->
            compact(T, [], [H | compact_fields(Fields, Elements)], Encoding)
    end.

compact_fields([], Elements) ->
    Elements;
compact_fields(Fields, Elements) ->
    [erl_syntax:binary(lists:reverse(Fields)) | Elements].

compact_strings(List) ->
    {String, Tail} = compact_strings(List, ""),
    {lists:reverse(String), Tail}.

compact_strings([], String) ->
    {String, []};
compact_strings([H|T], String) ->
    case erl_syntax:type(H) of
        string ->
            compact_strings(T, lists:reverse(erl_syntax:string_value(H), String));
        _ ->
            {String, [H|T]}
    end.

string_binary_field(String, Encoding) ->
    Types = encoding_to_binary_field_types(Encoding),
    erl_syntax:binary_field(erl_syntax:string(String), Types).

encoding_to_binary_field_types(latin1) -> [];
encoding_to_binary_field_types(unicode) ->
    encoding_to_binary_field_types(utf8);
encoding_to_binary_field_types(Encoding) when is_atom(Encoding) ->
    [erl_syntax:atom(Encoding)];
encoding_to_binary_field_types({Family, Endian}) ->
    [erl_syntax:atom(Family), erl_syntax:atom(Endian)].

get_option(Opt, St) ->
    proplists:get_value(Opt, St#state.options, default(Opt)).

default(encoding) -> ?DEFAULT_ENCODING;
default(output) -> beam;
default(_) -> undefined.

location(none) -> none;
location(Anno) ->
    erl_anno:line(Anno).

add_error(Anno, E, St) ->
    add_error(St#state.infile, Anno, E, St).

add_error(File, Anno, E, St) ->
    Loc = location(Anno),
    St#state{errors = [{File, {Loc,?MODULE,E}}|St#state.errors]}.

format_error({invalid_character, Encoding}) ->
    io_lib:fwrite("invalid character for encoding ~tw", [Encoding]);
format_error({error, ?MODULE, Error}) when is_list(Error) ->
    Error;
format_error({error, Module, Error}) ->
    Module:format_error(Error);
format_error({file_error, Reason}) ->
    io_lib:fwrite("~ts",[file:format_error(Reason)]).



%% Void elements must not have an end tag (</tag>) in HTML5, while for most
%% elements a proper end tag (<tag></tag>, not <tag />) is mandatory.
%%
%% http://www.w3.org/TR/html5/syntax.html#void-elements
%% http://www.w3.org/TR/html5/syntax.html#syntax-tag-omission

-define(self_closing, "/>"). % slash ignored in HTML5

html_end_tag(area) -> ?self_closing;
html_end_tag(base) -> ?self_closing;
html_end_tag(br) -> ?self_closing;
html_end_tag(col) -> ?self_closing;
html_end_tag(embed) -> ?self_closing;
html_end_tag(hr) -> ?self_closing;
html_end_tag(img) -> ?self_closing;
html_end_tag(input) -> ?self_closing;
html_end_tag(keygen) -> ?self_closing;
html_end_tag(link) -> ?self_closing;
html_end_tag(meta) -> ?self_closing;
html_end_tag(param) -> ?self_closing;
html_end_tag(source) -> ?self_closing;
html_end_tag(track) -> ?self_closing;
html_end_tag(wbr) -> ?self_closing;
html_end_tag(Tag) -> "></" ++ atom_to_list(Tag) ++ ">".
