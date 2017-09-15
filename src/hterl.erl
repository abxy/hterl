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
	St#state{forms = [compile_form(F, Opts) || F <- St#state.forms]}.


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


compile_form({function, Anno, Name, Arity, Clauses}, Opts) ->
	{function, Anno, Name, Arity, compile_clauses(Clauses, Opts)};
compile_form(Form, _Opts) ->
	Form.


compile_clauses(Clauses, Opts) ->
	[compile_clause(C, Opts) || C <- Clauses].

compile_clause({clause, Anno, Patterns, Guards, Body}, Opts) ->
	{clause, Anno, Patterns, Guards, compile_exprs(Body, Opts)}.

compile_exprs(Exprs, Opts) ->
	[compile_expr(E, Opts) || E <- Exprs].

compile_expr({tags, _, _} = TagsExpr, Opts) ->
	case proplists:get_bool(precompile, Opts) of
		true -> compile_tags_pre(TagsExpr, Opts);
		false -> compile_tags_ehtml(TagsExpr, Opts)
	end;
compile_expr({'case', Anno, Expr, Clauses}, Opts) ->
	{'case', Anno, compile_expr(Expr, Opts), compile_clauses(Clauses, Opts)};
compile_expr({'if', Anno, Clauses}, Opts) ->
	{'if', Anno, compile_clauses(Clauses, Opts)};
compile_expr({'receive', Anno, Clauses}, Opts) ->
	{'receive', Anno, compile_clauses(Clauses, Opts)};
compile_expr({block, Anno, Exprs}, Opts) ->
	{block, Anno, compile_exprs(Exprs, Opts)};
compile_expr({match, Anno, LHS, RHS}, Opts) ->
	{match, Anno, LHS, compile_expr(RHS, Opts)};
compile_expr({call, Anno, Fun, Args}, Opts) ->
	{call, Anno, Fun, compile_exprs(Args, Opts)};
compile_expr({lc, Anno, Expr, LcExprs}, Opts) ->
	{lc, Anno, compile_expr(Expr, Opts), LcExprs};
compile_expr({tuple, Anno, Exprs}, Opts) ->
	{tuple, Anno, compile_exprs(Exprs, Opts)};
compile_expr({cons, Anno, Head, Tail}, Opts) ->
	{cons, Anno, compile_expr(Head, Opts), compile_expr(Tail, Opts)};
compile_expr(Expr, _Opts) ->
	Expr.

compile_tags_ehtml({tags, Anno, Tags}, Opts) ->
	abstract_list([compile_tag_ehtml(T, Opts) || T <- Tags], Anno).

compile_tag_ehtml({tag, Anno, Name, [], []}, _Opts) ->
	{tuple, Anno, [
		{atom, Anno, Name}
	]};
compile_tag_ehtml({tag, Anno, Name, Attrs, []}, Opts) ->
	{tuple, Anno, [
		{atom, Anno, Name}, 
		compile_attrs(Attrs, Anno, Opts)
	]};
compile_tag_ehtml({tag, Anno, Name, Attrs, Exprs}, Opts) ->
	{tuple, Anno, [
		{atom, Anno, Name}, 
		compile_attrs(Attrs, Anno, Opts),
		abstract_list(compile_exprs(Exprs, Opts), Anno)
	]}.

compile_attrs(Attrs, Anno, Opts) ->
	abstract_list([compile_attr(Attr, Opts) || Attr <- Attrs], Anno).

compile_attr({min_attr, Anno, Name}, _Opts) ->
	{atom, Anno, Name};
compile_attr({attr, Anno, Name, Expr}, Opts) ->
	{tuple, Anno, [{atom, Anno, Name}, compile_expr(Expr, Opts)]}.

%% pre

compile_tags_pre({tags, Anno, Tags}, Opts) ->
	{tuple, Anno, [
		{atom, Anno, pre_html},
		compress(flatten(abstract_list([compile_tag_pre(T, Opts) || T <- Tags], Anno)))
	]}.

compile_tag_pre({tag, Anno, Name, Attrs, []}, Opts) ->
	abstract_list(
		[list_to_abstract_binary("<" ++ atom_to_list(Name), Anno)] ++
		[compile_attr_pre(Attr, Opts) || Attr <- Attrs] ++
		[list_to_abstract_binary("/>", Anno)]
	, Anno);
compile_tag_pre({tag, Anno, Name, Attrs, BodyExprs}, Opts) ->
	abstract_list(
		[list_to_abstract_binary("<" ++ atom_to_list(Name), Anno)] ++
		[compile_attr_pre(Attr, Opts) || Attr <- Attrs] ++
		[list_to_abstract_binary(">", Anno)] ++
		[compile_body_expr_pre(Expr, Opts) || Expr <- BodyExprs] ++
		[list_to_abstract_binary("</" ++ atom_to_list(Name) ++ ">", Anno)]
	, Anno).

compile_attr_pre({min_attr, Anno, Name}, _Opts) ->
	list_to_abstract_binary(" " ++ atom_to_list(Name), Anno);
compile_attr_pre({attr, Anno, Name, Expr}, Opts) ->
	abstract_list([
		list_to_abstract_binary(" " ++ atom_to_list(Name) ++ "=\"", Anno),
		compile_attr_expr_pre(Expr, Opts),
		list_to_abstract_binary("\"", Anno)
	], Anno).

compile_attr_expr_pre(Expr, Opts) ->
	case compile_expr(Expr, Opts) of
		{string, Anno, Str} ->
			erl_parse:abstract(hterl_api:htmlize(Str), Anno);
		{char, Anno, Ch} ->
			erl_parse:abstract(hterl_api:htmlize_char(Ch), Anno);
		{integer, Anno, Ch} when Ch >= 0 andalso Ch =< 255 ->
			erl_parse:abstract(hterl_api:htmlize_char(Ch), Anno);
		{bin, Anno, _} = BinAbs ->
			try
				Bin = erl_parse:normalise(BinAbs),
				erl_parse:abstract(hterl_api:htmlize(Bin), Anno)
			catch
				_:_ ->
					interpolate(BinAbs)
			end;
		CompiledExpr ->
			interpolate(CompiledExpr)
	end.

compile_body_expr_pre(Expr, Opts) ->
	case compile_expr(Expr, Opts) of
		{string, Anno, Str} ->
			erl_parse:abstract(hterl_api:htmlize(Str), Anno);
		{char, Anno, Ch} ->
			erl_parse:abstract(hterl_api:htmlize_char(Ch), Anno);
		{integer, Anno, Ch} when Ch >= 0 andalso Ch =< 255 ->
			erl_parse:abstract(hterl_api:htmlize_char(Ch), Anno);
		{bin, Anno, _} = BinAbs ->
			try
				Bin = erl_parse:normalise(BinAbs),
				erl_parse:abstract(hterl_api:htmlize(Bin), Anno)
			catch
				_:_ ->
					interpolate(BinAbs)
			end;
		{cons, Anno, H, T} ->
			{cons, Anno, compile_body_expr_pre(H, Opts), compile_body_expr_pre(T, Opts)};
		{nil, _} = Nil ->
			Nil;
		{lc, Anno, E, LcExprs} ->
			{lc, Anno, compile_body_expr_pre(E, Opts), LcExprs};
		{tuple, _, [{atom, _, pre_html}, T]} ->
			T;
		CompiledExpr ->
			interpolate(CompiledExpr)
	end.

interpolate(Expr) ->
	{call, 0, {remote, 0, {atom, 0, hterl_api}, {atom, 0, interpolate}}, [Expr]}.


compress(List) ->
	case compress([], List) of
		[Single] -> Single;
		Compressed -> abstract_list(Compressed, 0)
	end.


compress(DataPrefix, {nil, _}) ->
	[pretty_abstract_binary(iolist_to_binary(DataPrefix))];
compress(DataPrefix, {cons, _, H, T}) ->
	case extract_data(H) of
		error ->
			Bin = pretty_abstract_binary(iolist_to_binary(DataPrefix)),
			[Bin, H | compress([], T)];
		Data ->
			compress([DataPrefix|Data], T)
	end.

extract_data({char, _, Ch}) -> <<Ch>>;
extract_data({integer, _, Int}) -> <<Int>>;
extract_data({string, _, Ch}) -> Ch;
extract_data({bin, _, _} = BinAbs) ->
	% Must be normalisable, otherwise it would be wrapped in a call to interpolate.
	erl_parse:normalise(BinAbs);
extract_data(_) -> error.


pretty_abstract_binary(Bin) ->
	list_to_abstract_binary(binary_to_list(Bin), 0).


flatten(List) ->
	flatten_append(List, {nil, 0}).

flatten_append({cons, _Anno, {nil, _}, T}, Tail) ->
	flatten_append(T, Tail);
flatten_append({cons, _Anno, {cons, _, _, _} = H, T}, Tail) ->
	flatten_append(H, flatten_append(T, Tail));
flatten_append({cons, Anno, H, T}, Tail) ->
	{cons, Anno, H, flatten_append(T, Tail)};
flatten_append({nil, _}, Tail) ->
	Tail;
flatten_append(X, Tail) ->
	{cons, 0, X, Tail}.

list_to_abstract_binary(Str, Anno) when is_list(Str) ->
	{bin, Anno, [{bin_element, Anno, {string, Anno, Str}, default, default}]}.


abstract_list([], Anno) ->
	{nil, Anno};
abstract_list([X|Xs], Anno) ->
	{cons, Anno, X, abstract_list(Xs, Anno)}.

location(none) -> none;
location(Anno) ->
	erl_anno:line(Anno).

add_error(File, Anno, E, St) ->
	Loc = location(Anno),
	St#state{errors = [{File, {Loc,?MODULE,E}}|St#state.errors]}.


format_error({file_error, Reason}) ->
	io_lib:fwrite("~ts",[file:format_error(Reason)]).

