# Hyper-Text Erlang

Erlang extended with HTML-like tags in the expression syntax.
Aims to be a better (albeit less general) alternative to text template engines.
This is still a toy project and should not be considered ready for production.

## What is it?

The traditional approach to generating dynamic web pages is to use a template engine.
There are many to choose from and they all support substitutions, and to varying degrees data manipulations and flow control.
Composition is normally supported in the form of partial templates, which can be included in the main template using a special syntax.

Hyper-Text Erlang (Hterl) presents an alternative to this approach.
Hterl extends Erlang to include HTML tags in the expression syntax.
Instead of templates you write regular Erlang functions that return HTML.

```
bold(X) -> <b> X </b>.
```

Note the absence of substitution markers such as `<% %>` or `{{ }}` around the variable X.
Because HTML elements are part of the expression syntax, there is no need to switch back and forth between a text mode and code mode.

### Syntax

The syntax is not HTML, only HTML-like.

"HTML" elements can be written with an opening tag and a matching closing tag `<div> [...] </div>` or as a self-closing tag `<div/>` but never as an opening tag without a closing tag.
The reason is that the Hterl parser is not aware of which elements are considered _empty_ according to the HTML spec.

The body of an element is a comma separated list of expressions whose results are concatenated in the output.

```
greet(Name) ->
	<span> "Hello, ", <u> Name </u>, "!" </span>.
```

Given the above definition `greet("Joe")` evaluates to `<span>Hello, <u>Joe</u>!</span>`.
Note that the static strings are quoted. This is a logical consequence of the rule that says that the body of an element is an expression.

Elements that follow each other are concatenated into a single expression, therefore no comma is needed between the `<li>` elements in the following example.

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

Attributes are supported, and like element bodies their values are written as bare expressions
meaning literal strings have to be quoted, but variables do not. 

```
french_hello() ->
	<i lang="fr">"Bonjour le monde!"</i>.

link(Text, Url) ->
	<a href=Url>Text</a>.
```

Unlike element bodies, some expression forms need to be surrounded by parentheses when they appear as attributes.
Notably, function calls have this requirement.
This restriction may be relaxed in future.

There is no support for for HTML style comments `<!-- -->` but Erlang comments are fully supported.

```
erlang_comments() ->
    <p>
        % Erlang comments may appear inside tag bodies, ...
        "This is a paragraph of text"
        " which continues on the next line."        
    </p>
    % between tag bodies, ...
    <span
        % and even in the opening tag.
        style="background: pink;">
    </span>.
```

### Semantics

Values of the following types are valid in the body of an HTML element: strings, characters (i.e. integers between 0 and 255), binaries, and HTML elements.
Additionally lists of valid values are valid.

Because Hterl is only an extension of Erlang at the syntax level, the HTML elements have to be embedded in the existing universe of Erlang values.
This has already been done by EHTML in [Yaws](http://yaws.hyber.org/).
Hterl has two output modes and both are compatible with EHTML.
In the default mode `<p class="greeting"> "Hello, World!" </p>` is compiled to `{p, [{class, "greeting"}], ["Hello, World!"]}`, in the pre-compile mode
the same expression is compiled to `{pre_html, <<"<p class=\"greeting\">Hello, World!</p>">>}`.


## Use

Include hterl as a dependency in your rebar config, or add the [rebar3_hterl plugin](https://github.com/abxy/rebar3_hterl/).

```
{deps, [
    {hterl, {git, "https://github.com/abxy/hterl.git", {branch, "master"}}}
]}.
```

### Example

Create a file `test.hterl` with the following content.

```
-module(test).
-export([unordered_list/1]).

unordered_list(Xs) ->
	<ul>
		[ <li> X </li> || X <- Xs ]
	</ul>.
```

Compile and test.

```
1> hterl:file("test.hterl").
ok
2> c("test.erl").
{ok, test}
3> test:unordered_list(["One", "Two"]).
{ul,[],[[{li,[],["One"]},{li,[],["Two"]}]]}
```

Re-compile with option `precompile`.

```
4> hterl:file("test.hterl", [precompile]).
ok
5> c("test.erl").
{ok, test}
6> test:unordered_list(["One", "Two"]).
{pre_html,[<<"<ul>">>,
           [[<<"<li>">>,"One",<<"</li>">>],
            [<<"<li>">>,"Two",<<"</li>">>]],
           <<"</ul>">>]}
```

## Build

```
$ rebar3 compile
```
