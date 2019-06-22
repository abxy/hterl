-module(hterl_api).
-export([htmlize/1]).
-export([interpolate/2, interpolate_attr/2]).
-export([render/1, render/2]).
-export([print_exception/4]).

-import(unicode, [characters_to_binary/3, characters_to_list/2]).

%% htmlize
htmlize(Bin) when is_binary(Bin) ->
    list_to_binary(htmlize_l(binary_to_list(Bin)));
htmlize(List) when is_list(List) ->
    htmlize_l(List).

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
    Decoded = characters_to_list(Bin, Encoding),
    characters_to_binary(htmlize_l(Decoded), Encoding, Encoding);
interpolate(Tuple, Encoding) when is_tuple(Tuple) ->
    render(Tuple, Encoding).

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
    characters_to_binary(String, Encoding, Encoding);
interpolate_string(X, Acc, Encoding) ->
    String = lists:reverse(Acc),
    Binary = characters_to_binary(String, Encoding, Encoding),
    [Binary | interpolate(X, Encoding)].

interpolate_attr(Atom, Encoding) when is_atom(Atom) ->
    interpolate_attr(atom_to_list(Atom), Encoding);
interpolate_attr(Integer, Encoding) when is_integer(Integer) ->
    characters_to_binary(integer_to_list(Integer), latin1, Encoding);
interpolate_attr(String, Encoding) when is_list(String) ->
    characters_to_binary(htmlize_l(String), Encoding, Encoding);
interpolate_attr(Bin, Encoding) when is_binary(Bin) ->
    Decoded = characters_to_list(Bin, Encoding),
    characters_to_binary(htmlize_l(Decoded), Encoding, Encoding).

%% render

render(Element) ->
    render(Element, unicode).

render({Tag}, Encoding) ->
    characters_to_binary([$<, atom_to_list(Tag) | html_end_tag(Tag)], Encoding, Encoding);
render({pre_html, X}, _Encoding) -> X;
render({Tag, Attrs}, Encoding) ->
    [
        characters_to_binary([$< | atom_to_list(Tag)], Encoding, Encoding),
        render_attrs(Attrs, Encoding),
        characters_to_binary(html_end_tag(Tag), Encoding, Encoding)
    ];
render({Tag, Attrs, Body}, Encoding) ->
    TagStr = atom_to_list(Tag),
    [
        characters_to_binary([$< | TagStr], Encoding, Encoding),
        render_attrs(Attrs, Encoding),
        characters_to_binary(">", Encoding, Encoding),
        render(Body, Encoding),
        characters_to_binary([$<, $/, TagStr, $>], Encoding, Encoding)
    ];
render(X, Encoding) when not is_tuple(X) ->
    interpolate(X, Encoding).

render_attrs([], _Encoding) -> [];
render_attrs([Name|Attrs], Encoding) when is_atom(Name) ->
    Rendered = characters_to_binary([($ )|atom_to_list(Name)], Encoding, Encoding),
    [Rendered | render_attrs(Attrs, Encoding)];
render_attrs([{Name, Value}|Attrs], Encoding) ->
    Pre = characters_to_binary([($ ), atom_to_list(Name), $=, $"], Encoding, Encoding),
    Post = characters_to_binary("\"", Encoding, Encoding),
    RenderedValue = interpolate_attr(Value, Encoding),
    [Pre, RenderedValue, Post | render_attrs(Attrs, Encoding)].


%% print_exception
print_exception(Class, Error, Stacktrace, Encoding) ->
    render({pre, [{style, "background: red; color: white;"}],
        io_lib:print({Class, Error, Stacktrace})
    }, Encoding).

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
