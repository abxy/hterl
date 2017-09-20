-module(hterl).


-export([file/1, file/2]).

-export([report_error/1]).
-export([format_error/1]).


-record(state, {
	infile,
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
				St1 = St0#state{inport = Inport},
				passes(St1)
			after
				ok = file:close(Inport)
			end;
		{error, Reason} ->
			add_error(InFile, none, {file_error, Reason}, St0)
	end,
	hterl_ret(St).


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
	Errors = St#state.errors,
	case Errors of
		[] ->
			ok;
		_ ->
			error
	end.


passes(St) ->
	output(transform(parse(St))).

transform(St) ->
	Opts = St#state.options,
	St#state{forms = [erl_syntax:revert(rewrite(Form, Opts)) || Form <- St#state.forms]}.


output(St) ->
	#state{forms=Forms, outfile=OutFile} = St,
	file:write_file(OutFile, string:join([erl_pp:form(Form) || Form <- Forms], "\n")),
	St.


report_errors(St) ->
	lists:foreach(fun report_error/1, lists:sort(St#state.errors)).
	

report_error({File, {none, Mod, E}}) ->
	io:fwrite(<<"~ts: ~ts\n">>, [File,Mod:format_error(E)]);
report_error({File, {Line, Mod, E}}) ->
	io:fwrite(<<"~ts:~w: ~ts\n">>, [File,Line,Mod:format_error(E)]).


parse(St0) ->
	St = parse(St0#state.inport, 1, St0),
	St#state{forms = lists:reverse(St#state.forms)}.

parse(Inport, Line, St) ->
	{NextLine, Form} = read_form(Inport, Line),
	parse(Form, Inport, NextLine, St).


parse(eof, _Inport, _NextLine, St) ->
	St;
parse(Form, Inport, NextLine, St0) ->
	St = St0#state{forms = [Form | St0#state.forms]},
	parse(Inport, NextLine, St).


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
		list_unless_singleton(compact(flatten([rewrite_tag_pre(Tag, Opts) || Tag <- Tags])))
	]).

rewrite_tag_pre({tag, _Anno, Name, Attrs, []}, Opts) ->
	erl_syntax:list(
		[binary_from_string("<" ++ atom_to_list(Name), Opts)] ++
		[rewrite_attr_pre(Attr, Opts) || Attr <- Attrs] ++
		[binary_from_string(html_end_tag(Name), Opts)]
	);
rewrite_tag_pre({tag, _Anno, Name, Attrs, Body}, Opts) ->
	erl_syntax:list(
		[binary_from_string("<" ++ atom_to_list(Name), Opts)] ++
		[rewrite_attr_pre(Attr, Opts) || Attr <- Attrs] ++
		[binary_from_string(">", Opts)] ++
		[rewrite_body_expr_pre(Expr, Opts) || Expr <- Body] ++ 
		[binary_from_string("</" ++ atom_to_list(Name) ++ ">", Opts)]
	).

rewrite_attr_pre({min_attr, _Anno, Name}, Opts) ->
	binary_from_string(" " ++ atom_to_list(Name), Opts);
rewrite_attr_pre({attr, _Anno, Name, Expr}, Opts) ->
	erl_syntax:list([
		binary_from_string(" " ++ atom_to_list(Name) ++ "=\"", Opts),
		rewrite_attr_expr_pre(Expr, Opts),
		binary_from_string("\"", Opts)
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
		binary ->
			case erl_syntax:is_literal(Expr) of
				true ->
					erl_syntax:abstract(hterl_api:htmlize(erl_syntax:concrete(Expr)));
				false ->
					apply_interpolate(Expr)
			end;
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
		binary ->
			case erl_syntax:is_literal(Expr) of
				true ->
					erl_syntax:abstract(hterl_api:htmlize(erl_syntax:concrete(Expr)));
				false ->
					apply_interpolate_attr(Expr)
			end;
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

binary_from_string(String, _Opts) ->
	% The right thing to do would be to use erl_syntax:string
	% but erl_syntax:concrete has a bug that prevents that.
	erl_syntax:binary([erl_syntax:binary_field({string, 0, String})]).

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
	compact(List, []).

compact([], LiteralPrefix) ->
	[pretty_binary(LiteralPrefix)];
compact([H|T], LiteralPrefix) ->
	case literal_data(H) of
		not_literal ->
			Bin = pretty_binary(LiteralPrefix),
			[Bin, H | compact(T, [])];
		Literal ->
			compact(T, [LiteralPrefix|Literal])
	end.

pretty_binary(IoList) ->
	Bin = iolist_to_binary(IoList),
	binary_from_string(binary_to_list(Bin), []).

literal_data(Tree) ->
	Type = erl_syntax:type(Tree),
	case lists:member(Type, [string, char, integer, binary]) of
		true -> erl_syntax:concrete(Tree);
		false -> not_literal
	end.

location(none) -> none;
location(Anno) ->
	erl_anno:line(Anno).

add_error(File, Anno, E, St) ->
	Loc = location(Anno),
	St#state{errors = [{File, {Loc,?MODULE,E}}|St#state.errors]}.


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
