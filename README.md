# Hyper-Text Erlang

An extension for Erlang to support for "HTML" tags in the expression syntax.
This is still a toy project and should not be considered ready for production.

## Getting Started

Just clone the repo and build using rebar3.

```
$ rebar3 compile
```

### Prerequisites

Tag expressions in hterl evaluate to valid EHTML as defined by Yaws.
While not a strict prerequisite it is recommended to have Yaws installed for rendering the output.

## Example

Create a file test.hterl.

```
-module(test).
-export([unordered_list/1]).

unordered_list(Xs) ->
	<ul>
		[ <li> X </li> || X <- Xs ]
	</ul>.
```

Compile and test it.

```
1> hterl:file("test.hterl").
ok
2> Out = test:unordered_list(["One", "Two"]).
[{ul,[],[[[{li,[],["One"]}],[{li,[],["Two"]}]]]}]
```

The output is EHTML and can be rendered as HTML using a function from Yaws.

```
3> io:format("~ts~n", [yaws_api:ehtml_expand(Out)]).
<ul>
<li>One</li>
<li>Two</li></ul>
ok
```
For more examples check out [examples/demo.hterl](examples/demo.hterl).

## Syntax

The expression syntax of Erlang has been extended with tag expressions.
A tag expression consists of one or more tags following eachother.

A tag body can contain zero or more Erlang expressions, no escaping necessary.
The right-hand side of an attribute is a single Erlang expression, here parentheses are required for some expressions.
