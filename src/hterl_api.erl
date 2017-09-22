-module(hterl_api).
-export([htmlize/1, htmlize_char/1]).
-export([interpolate/2, interpolate_attr/2]).
-export([render/1, render/3]).

%% htmlize
htmlize(Bin) when is_binary(Bin) ->
    list_to_binary(htmlize_l(binary_to_list(Bin)));
htmlize(List) when is_list(List) ->
    htmlize_l(List).


htmlize_char($>) ->
    <<"&gt;">>;
htmlize_char($<) ->
    <<"&lt;">>;
htmlize_char($&) ->
    <<"&amp;">>;
htmlize_char($") ->
    <<"&quot;">>;
htmlize_char(X) ->
    X.


%% htmlize list (usually much more efficient than above)
htmlize_l(List) ->
    htmlize_l(List, []).

htmlize_l([], Acc) -> lists:reverse(Acc);
htmlize_l([$>|Tail], Acc) ->
    htmlize_l(Tail, [$;,$t,$g,$&|Acc]);
htmlize_l([$<|Tail], Acc) ->
    htmlize_l(Tail, [$;,$t,$l,$&|Acc]);
htmlize_l([$&|Tail], Acc) ->
    htmlize_l(Tail, [$;,$p,$m,$a,$&|Acc]);
htmlize_l([$"|Tail], Acc) ->
    htmlize_l(Tail, [$;,$t,$o,$u,$q,$&|Acc]);

htmlize_l([X|Tail], Acc) when is_integer(X) ->
    htmlize_l(Tail, [X|Acc]);
htmlize_l([X|Tail], Acc) when is_binary(X) ->
    X2 = htmlize_l(binary_to_list(X)),
    htmlize_l(Tail, [X2|Acc]);
htmlize_l([X|Tail], Ack) when is_list(X) ->
    X2 = htmlize_l(X),
htmlize_l(Tail, [X2|Ack]).

%% interpolate
interpolate(Ch, Encoding) when is_integer(Ch) ->
    interpolate_string([Ch], Encoding);
interpolate([H|_] = List, Encoding) when is_integer(H) ->
    interpolate_string(List, Encoding);
interpolate([H|T], Encoding) ->
    [interpolate(H, Encoding)|interpolate(T, Encoding)];
interpolate([], _Encoding) -> [];
interpolate({pre_html, X}, _Encoding) -> X;
interpolate(Bin, Encoding) when is_binary(Bin) ->
    Decoded = unicode:characters_to_list(Bin, Encoding),
    unicode:characters_to_binary(htmlize_l(Decoded), Encoding, Encoding).

interpolate_string(List, Encoding) ->
    interpolate_string(List, [], Encoding).

interpolate_string([$>|Tail], Acc, Encoding) ->
    interpolate_string(Tail, [$;,$t,$g,$&|Acc], Encoding);
interpolate_string([$<|Tail], Acc, Encoding) ->
    interpolate_string(Tail, [$;,$t,$l,$&|Acc], Encoding);
interpolate_string([$&|Tail], Acc, Encoding) ->
    interpolate_string(Tail, [$;,$p,$m,$a,$&|Acc], Encoding);
interpolate_string([$"|Tail], Acc, Encoding) ->
    interpolate_string(Tail, [$;,$t,$o,$u,$q,$&|Acc], Encoding);
interpolate_string([X|Tail], Acc, Encoding) when is_integer(X) ->
    interpolate_string(Tail, [X|Acc], Encoding);
interpolate_string([], Acc, Encoding) ->
    String = lists:reverse(Acc),
    unicode:characters_to_binary(String, Encoding, Encoding);
interpolate_string([_|_] = List, Acc, Encoding) ->
    String = lists:reverse(Acc),
    Binary = unicode:characters_to_binary(String, Encoding, Encoding),
    [Binary || interpolate(List, Encoding)].


interpolate_attr(Atom, Encoding) when is_atom(Atom) ->
    interpolate_attr(atom_to_list(Atom), Encoding);
interpolate_attr(Integer, Encoding) when is_integer(Integer) ->
    unicode:characters_to_binary(integer_to_list(Integer), latin1, Encoding);
interpolate_attr(String, Encoding) when is_list(String) ->
    unicode:characters_to_binary(htmlize_l(String), Encoding, Encoding).


value2string(Atom, _InEncoding, OutEncoding) when is_atom(Atom) ->
    atom_to_binary(Atom, OutEncoding);
value2string(String, InEncoding, OutEncoding) when is_list(String) ->
    unicode:characters_to_binary(String, InEncoding, OutEncoding);
value2string(Binary, _InEncoding, _OutEncoding) when is_binary(Binary) ->
    Binary;
value2string(Integer, _InEncoding, _OutEncoding) when is_integer(Integer) ->
    integer_to_list(Integer);
value2string(Float, _InEncoding, _OutEncoding) when is_float(Float) ->
    float_to_list(Float).

%% render

render(Element) ->
    render(Element, unicode, unicode).


render(Ch, _InEncoding, _OutEncoding) when Ch >= 0 andalso Ch =< 127 ->
    htmlize_char(Ch);
render(Ch, InEncoding, OutEncoding) when Ch >= 128 andalso Ch =< 255 ->
    unicode:characters_to_binary([Ch], InEncoding, OutEncoding);
render(Bin, _InEncoding, _OutEncoding) when is_binary(Bin) ->
    htmlize(Bin);
render({pre_html, String}, _InEncoding, _OutEncoding) ->
    String;
render({Tag}, _InEncoding, OutEncoding) ->
    [$<, atom_to_binary(Tag, OutEncoding) | html_end_tag(Tag)];
render({Tag, Attrs}, InEncoding, OutEncoding) ->
    TagString = atom_to_binary(Tag, OutEncoding),
    AttrsString = render_attrs(Attrs, InEncoding, OutEncoding),
    [$<, TagString, AttrsString | html_end_tag(Tag)];
render({Tag, Attrs, Body}, InEncoding, OutEncoding) ->
    TagString = atom_to_binary(Tag, OutEncoding),
    AttrsString = render_attrs(Attrs, InEncoding, OutEncoding),
    BodyString = render(Body, InEncoding, OutEncoding),
    [$<, TagString, AttrsString, $>, BodyString, $<, $/, TagString, $>];
render([], _InEncoding, _OutEncoding) ->
    [];
render([H|T], InEncoding, OutEncoding) ->
    [render(H, InEncoding, OutEncoding) | render(T, InEncoding, OutEncoding)].

render_attrs([], _InEnc, _OutEnc) -> [];
render_attrs([Attr|Tail], InEnc, OutEnc) when is_atom(Attr) ->
    [($ ), atom_to_binary(Attr, OutEnc) | render_attrs(Tail, InEnc, OutEnc)];
render_attrs([{Name, Value}|Tail], InEnc, OutEnc) when is_atom(Name) ->
    ValueStr = htmlize(value2string(Value, InEnc, OutEnc)),
    [($ ), atom_to_binary(Name, OutEnc), $=, $", ValueStr, $" | render_attrs(Tail, InEnc, OutEnc)].

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
