-module(hterl).


-export([file/1]).

-export([report_error/1]).
-export([format_error/1]).


-record(state, {
	inport,
	forms = [],
	errors = []
}).

%%====================================================================
%% API functions
%%====================================================================


file(Path) ->
	infile(Path, #state{}).

%%====================================================================
%% Internal functions
%%====================================================================


infile(Path, St0) ->
	St = case file:open(Path, [read, read_ahead]) of
		{ok, Inport} ->
			try
				St1 = St0#state{inport = Inport},
				passes(St1)
			after
				ok = file:close(Inport)
			end;
		{error, Reason} ->
			add_error(Path, none, {file_error, Reason}, St0)
	end,
	hterl_ret(St).

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
	St#state{forms = [compile_form(F) || F <- St#state.forms]}.


output(#state{forms=Forms} = St) ->
	case compile:forms(Forms) of
		{ok, ModuleName, Binary} ->			
			file:write_file(atom_to_list(ModuleName) ++ ".beam", Binary)
	end,
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


compile_form({function, Anno, Name, Arity, Clauses}) ->
	{function, Anno, Name, Arity, compile_clauses(Clauses)};
compile_form(Form) ->
	Form.


compile_clauses(Clauses) ->
	[compile_clause(C) || C <- Clauses].

compile_clause({clause, Anno, Patterns, Guards, Body}) ->
	{clause, Anno, Patterns, Guards, compile_exprs(Body)}.

compile_exprs(Exprs) ->
	[compile_expr(E) || E <- Exprs].

compile_expr({tags, Anno, Tags}) ->
	abstract_list([compile_tag(T) || T <- Tags], Anno);
compile_expr({'case', Anno, Expr, Clauses}) ->
	{'case', Anno, compile_expr(Expr), compile_clauses(Clauses)};
compile_expr({'if', Anno, Clauses}) ->
	{'if', Anno, compile_clauses(Clauses)};
compile_expr({'receive', Anno, Clauses}) ->
	{'receive', Anno, compile_clauses(Clauses)};
compile_expr({block, Anno, Exprs}) ->
	{block, Anno, compile_exprs(Exprs)};
compile_expr({match, Anno, LHS, RHS}) ->
	{match, Anno, LHS, compile_expr(RHS)};
compile_expr({call, Anno, Fun, Args}) ->
	{call, Anno, Fun, compile_exprs(Args)};
compile_expr({lc, Anno, Expr, LcExprs}) ->
	{lc, Anno, compile_expr(Expr), LcExprs};
compile_expr({tuple, Anno, Exprs}) ->
	{tuple, Anno, compile_exprs(Exprs)};
compile_expr({cons, Anno, Head, Tail}) ->
	{cons, Anno, compile_expr(Head), compile_expr(Tail)};
compile_expr(Expr) ->
	Expr.


compile_tag({tag, Anno, Name, Attrs, Exprs}) ->
	{tuple, Anno, [
		{atom, Anno, Name}, 
		compile_attrs(Attrs, Anno),
		abstract_list(compile_exprs(Exprs), Anno)
	]}.


compile_attrs(Attrs, Anno) ->
	abstract_list([compile_attr(Attr) || Attr <- Attrs], Anno).

compile_attr({min_attr, Anno, Name}) ->
	{atom, Anno, Name};
compile_attr({attr, Anno, Name, Expr}) ->
	{tuple, Anno, [{atom, Anno, Name}, compile_expr(Expr)]}.


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

