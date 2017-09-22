-module(hterl).


-export([file/1, file/2]).

-export([report_error/1]).
-export([format_error/1]).


-record(state, {
    infile,
    encoding,
    inport,
    outfile,
    forms = [],
    errors = [],
    options = []
}).

%%====================================================================
%% API functions
%%====================================================================

file(Path) ->
    file(Path, []).

file(Path, Options) ->
    St = start(Path, Options),
    infile(St).

%%====================================================================
%% Internal functions
%%====================================================================

start(InFileX, Options) ->
    InFile = assure_extension(InFileX, ".hterl"),
    OutFileX = filename:rootname(InFile, ".hterl"),
    OutFile = assure_extension(OutFileX, ".erl"),
    #state{
        infile = InFile,
        outfile = OutFile,
        options = Options
    }.

infile(St0) ->
    InFile = St0#state.infile,
    St = case file:open(InFile, [read, read_ahead]) of
        {ok, Inport} ->
            try
                Encoding = select_encoding(Inport),
                St1 = St0#state{inport = Inport, encoding = Encoding},
                passes(St1)
            after
                ok = file:close(Inport)
            end;
        {error, Reason} ->
            add_error(InFile, none, {file_error, Reason}, St0)
    end,
    case has_errors(St) of
        true -> file:delete(St#state.outfile), ok;
        false -> ok
    end,
    hterl_ret(St).

select_encoding(Inport) ->
    % Set port encoding, defaulting to utf8 (epp's default)
    % unless overridden by a directive in the file.
    EncodingOverride = epp:set_encoding(Inport),
    case EncodingOverride of
        none -> epp:default_encoding();
        Encoding -> Encoding
    end.

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
    case has_errors(St) of
        false -> ok;
        true -> error
    end.

has_errors(#state{errors = []}) -> false;
has_errors(_) -> true.


passes(St) ->
    output(transform(parse(St))).

transform(St) ->
    Opts = St#state.options,
    St#state{forms = [erl_syntax:revert(rewrite(Form, Opts)) || Form <- St#state.forms]}.


output(St) ->
    #state{forms=Forms, outfile=OutFile} = St,
    case file:open(OutFile, [write, delayed_write]) of
        {ok, OutPort} ->
            try
                set_encoding(OutPort, St#state.encoding),
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

set_encoding(Port, Encoding) ->
    ok = io:setopts(Port, [{encoding, Encoding}]).

report_errors(St) ->
    lists:foreach(fun report_error/1, lists:sort(St#state.errors)).


report_error({File, {none, Mod, E}}) ->
    io:fwrite(<<"~ts: ~ts\n">>, [File,Mod:format_error(E)]);
report_error({File, {Line, Mod, E}}) ->
    io:fwrite(<<"~ts:~w: ~ts\n">>, [File,Line,Mod:format_error(E)]).


parse(St0) ->
    St = parse_next(St0#state.inport, 1, St0),
    St#state{forms = lists:reverse(St#state.forms)}.

parse_next(Inport, Line, St0) ->
    {NextLine, Form} = read_form(Inport, Line),
    case parse(Form, St0) of
        {eof, St} -> St;
        St -> parse_next(Inport, NextLine, St)
    end.


parse(eof, St) ->
    {eof, St};
parse({error, ErrorLine, Error}, St0) ->
    add_error(erl_anno:new(ErrorLine), Error, St0);
parse(Form, St0) ->
    St0#state{forms = [Form | St0#state.forms]}.


read_form(Inport, Line) ->
    case hterl_scan:scan(Inport, '', Line) of
        {eof, NextLine} ->
            {NextLine, eof};
        {ok, Input, NextLine} ->
            {NextLine, case hterl_parser:parse(Input) of
                {error, {ErrorLine, Mod, Message}} ->
                    {error, ErrorLine, {error, Mod, Message}};
                {ok, Form} ->
                    Form
            end}
    end.

rewrite({tags, _Anno, Tags}, Opts) ->
    case proplists:get_bool(precompile, Opts) of
        true -> rewrite_tags_pre(Tags, Opts);
        false -> rewrite_tags_ehtml(Tags, Opts)
    end;
rewrite(Tree, Opts) ->
    Fun = fun (T) -> rewrite(T, Opts) end,
    erl_syntax_lib:map_subtrees(Fun, Tree).


rewrite_tags_ehtml(Tags, Opts) ->
    list_unless_singleton([rewrite_tag_ehtml(Tag, Opts) || Tag <- Tags]).

rewrite_tag_ehtml({tag, _Anno, Name, [], []}, _Opts) ->
    erl_syntax:tuple([erl_syntax:atom(Name)]);
rewrite_tag_ehtml({tag, _Anno, Name, Attrs, []}, Opts) ->
    erl_syntax:tuple([
        erl_syntax:atom(Name),
        rewrite_attrs_ehtml(Attrs, Opts)
    ]);
rewrite_tag_ehtml({tag, _Anno, Name, Attrs, Body}, Opts) ->
    erl_syntax:tuple([
        erl_syntax:atom(Name),
        rewrite_attrs_ehtml(Attrs, Opts),
        list_unless_singleton([rewrite(Expr, Opts) || Expr <- Body])
    ]).

rewrite_attrs_ehtml(Attrs, Opts) ->
    erl_syntax:list([rewrite_attr_ehtml(Attr, Opts) || Attr <- Attrs]).

rewrite_attr_ehtml({min_attr, _Anno, Name}, _Opts) ->
    erl_syntax:atom(Name);
rewrite_attr_ehtml({attr, _Anno, Name, Expr}, Opts) ->
    erl_syntax:tuple([erl_syntax:atom(Name), rewrite(Expr, Opts)]).

rewrite_tags_pre(Tags, Opts) ->
    erl_syntax:tuple([
        erl_syntax:atom(pre_html),
        compact(flatten([rewrite_tag_pre(Tag, Opts) || Tag <- Tags]))
    ]).

rewrite_tag_pre({tag, _Anno, Name, Attrs, []}, Opts) ->
    erl_syntax:list(
        [erl_syntax:string("<" ++ atom_to_list(Name))] ++
        [rewrite_attr_pre(Attr, Opts) || Attr <- Attrs] ++
        [erl_syntax:string(html_end_tag(Name))]
    );
rewrite_tag_pre({tag, _Anno, Name, Attrs, Body}, Opts) ->
    erl_syntax:list(
        [erl_syntax:string("<" ++ atom_to_list(Name))] ++
        [rewrite_attr_pre(Attr, Opts) || Attr <- Attrs] ++
        [erl_syntax:string(">")] ++
        [rewrite_body_expr_pre(Expr, Opts) || Expr <- Body] ++
        [erl_syntax:string("</" ++ atom_to_list(Name) ++ ">")]
    ).

rewrite_attr_pre({min_attr, _Anno, Name}, _Opts) ->
    erl_syntax:string(" " ++ atom_to_list(Name));
rewrite_attr_pre({attr, _Anno, Name, Expr}, Opts) ->
    erl_syntax:list([
        erl_syntax:string(" " ++ atom_to_list(Name) ++ "=\""),
        rewrite_attr_expr_pre(Expr, Opts),
        erl_syntax:string("\"")
    ]).

rewrite_body_expr_pre(SourceExpr, Opts) ->
    Expr = rewrite(SourceExpr, Opts),
    case erl_syntax:type(Expr) of
        string ->
            erl_syntax:string(hterl_api:htmlize(erl_syntax:string_value(Expr)));
        char ->
            erl_syntax:string(hterl_api:htmlize([erl_syntax:char_value(Expr)]));
        integer ->
            case erl_syntax:integer_value(Expr) of
                Ch when Ch >= 0 andalso Ch =< 255 ->
                    erl_syntax:string(hterl_api:htmlize([Ch]));
                _ ->
                    apply_interpolate(Expr)
            end;
        nil ->
            erl_syntax:nil();
        list ->
            Elems = erl_syntax:list_elements(Expr),
            erl_syntax:list([rewrite_body_expr_pre(E, Opts) || E <- Elems]);
        tuple ->
            case erl_syntax:tuple_elements(Expr) of
                [First, Second] ->
                    case erl_syntax:is_atom(First, pre_html) of
                        true -> Second;
                        false -> apply_interpolate(Expr)
                    end;
                _ ->
                    apply_interpolate(Expr)
            end;
        list_comp ->
            erl_syntax:list_comp(
                rewrite_body_expr_pre(erl_syntax:list_comp_template(Expr), Opts),
                erl_syntax:list_comp_body(Expr)
            );
        _ ->
            apply_interpolate(Expr)
    end.

rewrite_attr_expr_pre(SourceExpr, Opts) ->
    Expr = rewrite(SourceExpr, Opts),
    case erl_syntax:type(Expr) of
        string ->
            erl_syntax:string(hterl_api:htmlize(erl_syntax:string_value(Expr)));
        char ->
            erl_syntax:string(integer_to_list(erl_syntax:char_value(Expr)));
        integer ->
            erl_syntax:string(integer_to_list(erl_syntax:integer_value(Expr)));
        _ -> apply_interpolate_attr(Expr)
    end.

apply_interpolate_attr(Argument) ->
    erl_syntax:application(
        erl_syntax:atom(hterl_api),
        erl_syntax:atom(interpolate_attr),
        [Argument]).

apply_interpolate(Argument) ->
    erl_syntax:application(
        erl_syntax:atom(hterl_api),
        erl_syntax:atom(interpolate),
        [Argument]).

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

compact(List) ->
    Elements = compact(List, [], []),
    list_unless_singleton(lists:reverse(Elements)).

compact([], Fields, Elements) ->
    compact_fields(Fields, Elements);
compact([H|T], Fields, Elements) ->
    case erl_syntax:type(H) of
        string ->
            compact(T, [erl_syntax:binary_field(H) | Fields], Elements);
        binary ->
            compact(T, lists:reverse(erl_syntax:binary_fields(H), Fields), Elements);
        _ ->
            compact(T, [], [H | compact_fields(Fields, Elements)])
    end.

compact_fields([], Elements) ->
    Elements;
compact_fields(Fields, Elements) ->
    [erl_syntax:binary(lists:reverse(Fields)) | Elements].

location(none) -> none;
location(Anno) ->
    erl_anno:line(Anno).

add_error(Anno, E, St) ->
    add_error(St#state.infile, Anno, E, St).

add_error(File, Anno, E, St) ->
    Loc = location(Anno),
    St#state{errors = [{File, {Loc,?MODULE,E}}|St#state.errors]}.

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
