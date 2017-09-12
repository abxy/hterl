-module(hterl_scan).

-export([scan/1, scan/3]).

scan(Inport) ->
	scan(Inport, '', 1).

scan(Inport, Prompt, Line1) ->
	case catch io:scan_erl_form(Inport, Prompt, Line1, [return_white_spaces]) of
		{eof, Line2} ->
			{eof, Line2};
		{ok, Tokens, Line2} ->
			case lex(Tokens) of
				[] ->
					% lex removed all tokens (white_space) so we try another scan.
					scan(Inport, Prompt, Line2);
				LexedTokens ->
					{ok, LexedTokens, Line2}
			end;
		{error, Reason} ->
			{error, Reason};
		{error, Descriptor, Line2} ->
			{error, Descriptor, Line2};
		{'EXIT', Why} ->
			io:format('hterl_scan: Error scanning input line ~w~n', [Line1]),
			exit(Why)
	end.

% lex/1 defines a second lexing pass whose main purpose is to to disambiguate
% between the less than operator and start of tags, it uses white_space to do so.
% I.e. "<atom" is parsed as a single tag_start token while "< atom" is parsed as
% the operator < followed by an atom.
% It also strips the output of any remaining white_space tokens and combines
% "</" and "/>" to distinct tokens.

lex([]) ->
	[];
lex([{'<', Line}, {'/', Line} | Tokens]) ->
	[{'</', Line} | lex(Tokens)];
lex([{'<', Line}, {atom, Line, Symbol} | Tokens]) ->
	[{tag_start, Line, Symbol} | lex(Tokens)];
lex([{'/', Line}, {'>', Line} | Tokens]) ->
	[{'/>', Line} | lex(Tokens)];	
lex([{white_space, _Line, _Symbol} | Tokens]) ->
	lex(Tokens);
lex([Token | Tokens]) ->
	[Token | lex(Tokens)].
	



