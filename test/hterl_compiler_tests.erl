-module(hterl_compiler_tests).
-include_lib("eunit/include/eunit.hrl").

hterl_compiler_test_() ->
    [
        test_ex_testing([]),
        test_ex_testing([precompile, {encoding, utf8}])
    ].

test_ex_testing(Options) ->
    {setup,
        fun () -> compile_from_examples("ex_testing", Options) end,
        [
            fun test_integers_in_body/0,
            fun test_strings_in_body/0,
            fun test_binaries_in_body/0,
            fun test_pre_html_in_body/0,

            fun test_integer_attributes/0,
            fun test_string_attributes/0,
            fun test_atom_attributes/0,
            fun test_binary_attributes/0
        ]
    }.

test_integers_in_body() ->
    ?assertMatch(
        <<"<p>AAA&lt;&lt;&lt;</p>"/utf8>>,
        render_binary(ex_testing:integers_in_body(), utf8)).

test_strings_in_body() ->
    ?assertMatch(
        <<"<p>AAA&lt;&lt;&lt;</p>"/utf8>>,
        render_binary(ex_testing:strings_in_body(), utf8)).

test_binaries_in_body() ->
    ?assertEqual(
        <<"<p>AÖ 漢字 🔥AÖ 漢字 🔥</p>"/utf8>>,
        render_binary(ex_testing:binaries_in_body(), utf8)).

test_pre_html_in_body() ->
    ?assertMatch(
        <<"<p>"/utf8, 0, 255, 0, 255, 0, 255, "</p>"/utf8>>,
        render_binary(ex_testing:pre_html_in_body(), utf8)).

test_integer_attributes() ->
    ?assertEqual(
        <<"<p attr=\"65\" attr=\"65\" attr=\"65\"></p>"/utf8>>,
        render_binary(ex_testing:integer_attributes(), utf8)).

test_string_attributes() ->
    ?assertEqual(
        <<"<p attr=\"String\" attr=\"String\"></p>"/utf8>>,
        render_binary(ex_testing:string_attributes(), utf8)).

test_atom_attributes() ->
    ?assertEqual(
        <<"<p attr=\"atom\" attr=\"atom\"></p>"/utf8>>,
        render_binary(ex_testing:atom_attributes(), utf8)).

test_binary_attributes() ->
    ?assertEqual(
        <<"<p attr=\"binary\" attr=\"binary\"></p>"/utf8>>,
        render_binary(ex_testing:binary_attributes(), utf8)).

prerender_test() ->
    compile_from_examples("ex_testing", [precompile, {encoding, utf8}]),
    Expect = {pre_html, <<"<p>ABC<b></b>ABC<b></b></p><p></p>"/utf8>>},
    ?assertEqual(Expect, ex_testing:prerender()).

%-------------------------------------------------------------------------------
% Tests

prerender_unicode_latin1_test() ->
    % ex_unicode contains characters that are invalid in latin1 so it should fail to compile
    CompilerResult = hterl:file(from_examples_dir("ex_unicode"), [precompile, {encoding, latin1}]),
    ?assertNotMatch(ok, CompilerResult).

prerender_unicode_utf8_test() ->
    compile_from_examples("ex_unicode", [precompile, {encoding, utf8}]),
    ?assertMatch({pre_html, <<"<p>abc åäö 漢字 🔥</p>"/utf8>>}, ex_unicode:test()).

prerender_unicode_utf16_test() ->
    compile_from_examples("ex_unicode", [precompile, {encoding, utf16}]),
    ?assertMatch({pre_html, <<"<p>abc åäö 漢字 🔥</p>"/utf16-big>>}, ex_unicode:test()).

prerender_unicode_utf32_test() ->
    compile_from_examples("ex_unicode", [precompile, {encoding, utf32}]),
    ?assertMatch({pre_html, <<"<p>abc åäö 漢字 🔥</p>"/utf32-big>>}, ex_unicode:test()).

prerender_unicode_utf16_little_test() ->
    compile_from_examples("ex_unicode", [precompile, {encoding, {utf16, little}}]),
    ?assertMatch({pre_html, <<"<p>abc åäö 漢字 🔥</p>"/utf16-little>>}, ex_unicode:test()).

prerender_unicode_utf32_little_test() ->
    compile_from_examples("ex_unicode", [precompile, {encoding, {utf32, little}}]),
    ?assertMatch({pre_html, <<"<p>abc åäö 漢字 🔥</p>"/utf32-little>>}, ex_unicode:test()).


%-------------------------------------------------------------------------------
% Helpers

render_binary(X, Encoding) ->
    iolist_to_binary(hterl_api:render(X, Encoding)).

compile_from_examples(File, Options) ->
    compile(from_examples_dir(File), Options).

compile(File, Options) ->
    ok = hterl:file(File, [{output, erl}] ++ Options),
    {ok, Module, Binary} = compile:file(File, [binary]),
    {module, Module} = code:load_binary(Module, File, Binary).

from_examples_dir(File) ->
    {ok, Cwd} = file:get_cwd(),
    filename:join([Cwd, "examples", File]).
