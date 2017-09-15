-module(demo).

-compile(export_all).

bold(X) ->
    {pre_html,[<<"<b>">>,hterl_api:interpolate(X),<<"</b>">>]}.

hello() ->
    {pre_html,<<"<i>Hello, World!</i>">>}.

nested() ->
    {pre_html,<<"<h3>Title</h3><ul><li>1</li><li>2</li></ul>">>}.

greet(Name) ->
    {pre_html,
     [<<"<span>Hello, <u>">>,
      hterl_api:interpolate(Name),
      <<"</u>!</span>">>]}.

greet_alt(Name) ->
    ["Hello, ",
     {pre_html,[<<"<u>">>,hterl_api:interpolate(Name),<<"</u>">>]},
     "!"].

table(Headers, Rows) ->
    {pre_html,
     [<<"<table>">>,
      hterl_api:interpolate(table_head(Headers)),
      <<"<tbody>">>,
      hterl_api:interpolate(lists:map(fun data_row/1, Rows)),
      <<"</tbody></table>">>]}.

data_row(Data) ->
    {pre_html,
     [<<"<tr>">>,
      [ 
       [<<"<td>">>,hterl_api:interpolate(X),<<"</td>">>] ||
           X <- Data
      ],
      <<"</tr>">>]}.

table_head(Headers) ->
    UppercaseHeaders = lists:map(fun string:to_upper/1, Headers),
    {pre_html,
     [<<"<thead><tr>">>,
      [ 
       [<<"<th>">>,hterl_api:interpolate(H),<<"</th>">>] ||
           H <- UppercaseHeaders
      ],
      <<"</tr></thead>">>]}.

french_hello() ->
    {pre_html,<<"<i lang=\"fr\">Bonjour le monde!</i>">>}.

web_link(Text, Url) ->
    {pre_html,
     [<<"<a href=\"">>,
      hterl_api:interpolate(Url),
      <<"\">">>,
      hterl_api:interpolate(Text),
      <<"</a>">>]}.
