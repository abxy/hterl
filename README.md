Hypertext Erlang
================

[![Hex.pm](https://img.shields.io/hexpm/v/hterl.svg?style=flat)](https://hex.pm/packages/hterl)

A compiler for Hypertext Erlang.

What?
-----

Hypertext Erlang is Erlang extended with HTML-like tags in
the expression syntax.

The intended purpose is to provide a better alternative to text templating
engines for generating dynamic web pages.

With Hypertext Erlang you write functions that return HTML.
The syntax encourages composition by making it seamless to call other
functions that return HTML themselves; and it works beautifully with
list comprehensions and the rest of Erlangs syntax.

Here is a small example of how Hypertext Erlang can be used to render
a table.

```
results_table(Results) ->
    SortedResults = lists:sort(Results),
    <table>
        <thead>
            <tr>
                <th>"Time (mm:ss)"</th>
                <th>"Player"</th>
            </tr>
        </thead>
        <tbody>
            [results_row(Result) || Result <- SortedResults]
        </tbody>
    </table>.

results_row({Time, Player}) ->
    <tr>
        <td>Time</td>
        <td>Player</td>
    </tr>.
```

Note the absence of substitution markers such as `<% %>` or `{{ }}` around variable names like `Time` and `Player`.
That is because the body of a tag expression can contain any expression, not just other tag expressions.
This rule also explains why the header texts `"Time (mm:ss)"` and `"Player"` are quoted&mdash;that's simply how strings are written in Erlang.
See [Syntax](#syntax) for more.

Usage
-----

Include `hterl` as a dependency in your `rebar.config`, and add the `rebar3_hterl` plugin (found in a [separate repository](https://github.com/abxy/rebar3_hterl/)).

```
{deps, [{hterl, "0.10.0"}]}.

{plugins, [rebar3_hterl]}.
```

The plugin registers as a compiler for `.hterl` files, so `rebar3 compile` and all the rest of the rebar commands should just work.

Create Hypertext Erlang modules in `src/` or a sub-folder, name the source files something like `example.hterl`.

Here is a tiny example to get you started.

```
-module(example).

-export([unordered_list/1]).

unordered_list(Xs) ->
	<ul>
		[<li> X </li> || X <- Xs]
	</ul>.
```

Run `rebar3 shell` to compile the application and start a shell.
In the shell, you can use.

```
1> hterl:render_binary(example:unordered_list(["One", "Two", "Three"])).
<<"<ul><li>One</li><li>Two</li><li>Three</li></ul>">>
```

**Note:** Normally you would use `hterl:render/1` which returns `iodata()` and to unnecessary copying, but a binary is easier to read so it's used here.

If you're interested you can also see

```
1> example:unordered_list(["One", "Two", "Three"]).
{pre_html, [<<"<ul>">>, [
	[<<"li">>, <<"One">>, <<"</li>">>],
	[<<"li">>, <<"Two">>, <<"</li>">>],
	[<<"li">>, <<"Three">>, <<"</li>">>]
], <<"</ul>">>]}
```

Implementation
--------------

Hypertext Erlang is based on the official Erlang toolchain,
re-using as much as possible.
Tokenization is done using Erlang's scanner, followed by
a post-processing step to rewrite some token sequences. <!-- For instance, a `<` token followed by an `{atom, "h1"}` token is fused to a `{tag_start, "h1"}` token. -->
The parser is generated using `yecc` and a modified copy of the Erlang grammar.
The compiler works by transforming syntax tree containing tag-expressions to
a plain Erlang parse tree, which is then compiled using Erlang's compiler.

Tag expressions are compiled to expressions that construct `iodata()` directly.



Syntax
======

The syntax is not quite HTML, but it should be familiar enough.
This section explains the different syntax rules with examples for each.

Tags
----

Tag expressions be written with an opening tag and a _matching_ closing tag `<div> [...] </div>`
or as a self-closing tag `<br />` but never as an opening tag without a closing tag.
This is because the parser is not aware of which elements are considered _empty_
according to the HTML spec.


Body
----

The body of an element is a comma separated list of expressions whose results are concatenated in the output.

```
greet(Name) ->
    <span> "Hello, ", <u> Name </u>, "!" </span>.
```

Given the above definition `greet("Joe")` renders `<span>Hello, <u>Joe</u>!</span>`.
Note that the text in the body of an element has to be quoted.
This is a logical consequence of the rule that says that any expression is allowed in the body of an tag expression.

Whitespace
----------
Spaces and line breaks, in and around tags, are ignored. If you want the output to contain space between elements in the body, you have to explicitly include it.

```
whitespace(Name) ->
    <div>
        <span></span>, " ", <span></span>
    </div>.
```

Concatenation
-------------

Adjacent tag expressions are concatenated into a single expression, therefore no comma is needed between the `<li>` elements below.

```
prizes() ->
    <ol>
        <li>"Gold Medal"</li>
        <li>"Silver Medal"</li>
        <li>"Bronze Medal"</li>
    </ol>.
```

The concatenation rule is enabled everywhere, not just within element bodies.

```
definition(Term, Definition) ->
    <dt>Term</dt>
    <dd>Definition</dd>.

```

If this upsets you, consider that many programming languages, including Erlang, concatenate strings in a similar fashion.

```
strings() ->
    "These two strings are "
    "concatenated into one.".

```

Attributes
----------

Attribute values are also written as bare expressions,
meaning literal strings have to be quoted, but variables do not.

```
french_hello() ->
    <i lang="fr">"Bonjour le monde!"</i>.

link(Text, Url) ->
    <a href=Url>Text</a>.
```

Some expression forms need to be surrounded by parentheses when they appear as attributes.
Notably, function calls have this requirement.

```
message(Type, Content) ->
    <span class=(message_class(Type))>Content</span>.

message_class(error) ->
    "message message-error";
message_class(_) ->
    "message".
```

Hypertext Erlang requires all attribute names to be valid Erlang atoms.
In practice, this means that you have to quote attributes that contain dashes like `aria-labelledby`.

```
dialog(Header, Content) ->
	<div role="dialog" 'aria-labelledby'="dialogheader">
		<h2 id="dialogheader">Header</h2>,
		Content
	</div>.
```

Comments
--------

There is no support for for HTML style comments `<!-- -->`, but Erlang comments are fully supported.

```
erlang_comments() ->
    <p>
        % Erlang comments may appear inside element bodies, ...
        "This is a paragraph of text"
        " which continues on the next line."
    </p>
    % between elements, ...
    <span
        % and even in the opening tag.
        style="background: pink;">
    </span>.
```

Options
=======

* `output` (default: `beam`): Sets the output format, possible values are `beam` and `erl`.
* `outdir` (Optional): If set to a directory path, the output files will be put in this directory. Only relevant in standalone mode as the `rebar3_hterl` plugin overrides it.
