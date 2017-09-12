# Hyper-Text Erlang

An extension for Erlang to support for "HTML" tags in the expression syntax.
This is still a toy project and should not be considered ready for production.

## Getting Started

Just clone the repo and build using rebar3.

```
$ rebar3 compile
```

### Prerequisites

Tag expressions in hterl evaluate to valid EHTML as defined by `yaws`.
While not a strict prerequisite it is recommended to have `yaws`installed for rendering the output.

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

Compile the file using

```

1> hterl:file("test.hterl").

```

## Syntax

The expression syntax of Erlang has been extended with tag expressions.
A tag expression consists of one or more tags following eachother.

A tag body can contain zero or more Erlang expressions, no escaping necessary.
The right-hand side of an attribute is a single Erlang expression, here parentheses are required for some expressions.
