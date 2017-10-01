-module(hterl_compiler_tests).
-include_lib("eunit/include/eunit.hrl").


%-------------------------------------------------------------------------------
% Tests

prerender_unicode_little_test() ->
    ?assertNotMatch(ok, hterl:file(from_examples_dir("ex_unicode"), [precompile, {encoding, latin1}])).

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

compile_from_examples(File, Options) ->
    compile(from_examples_dir(File), Options).

compile(File, Options) ->
    ok = hterl:file(File, Options),
    {ok, Module, Binary} = compile:file(File, [binary]),
    {module, Module} = code:load_binary(Module, File, Binary).

from_examples_dir(File) ->
    {ok, Cwd} = file:get_cwd(),
    filename:join([Cwd, "examples", File]).
