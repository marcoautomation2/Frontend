package typeSystem;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.junit.jupiter.api.Test;

import core.LiteralDeclarations;

public final class TypeSystemTest extends testUtils.FearlessTestBase{
  static void ok(List<String> input){ typeOk(input); }
  static void fail(String expected, List<String> input){ typeFail(expected, input); }
  static void failExt(String expected, List<String> input){ typeFailRaw(expected, input); }
  static void failWf(String expected, List<String> input){ typeFailRaw("In file: [###].fear\n\n"+expected+"Error 7 WellFormedness", input); }

@Test void tsMiniOk(){ok(List.of("""
A:{.foo123:A->this.foo123}
"""));}
@Test void anonLiteralInDuplicatedBody(){ok(List.of("""
A:{ .k: A -> this }
T0:{ .m: A; }
T1:T0{ read .m: A -> A }
U:{ .u: T1 -> T1{ .m: A -> A{ .k: A -> A } } }
"""));}
@Test void manyConsecutiveLetsInOneMethod(){
  var lets= IntStream.rangeClosed(1, 150).mapToObj(i -> ".let x"+i+"= {5} ").collect(Collectors.joining());
  ok(List.of("use base.Nat as Nat; User:{ .u: Nat -> base.Block#"+lets+".return {x150} }"));}
@Test void manyNestedLiterals(){
  var open= IntStream.range(0, 300).mapToObj(_ -> "A{ .a -> ").collect(Collectors.joining());
  ok(List.of("A:{ .a: A } User:{ .u: A -> "+open+"A{ .a -> this.u }"+" }".repeat(300)+" }"));}
@Test void expansiveSupertypeArgumentNotASubtype(){fail("""
002| T1:T0[T0[T1]]{ .m(a: T0[T1]): T1 -> this.m(this) }
   |                ---------------------~~~~^^^~~~~~

While inspecting ".m(_)" line 2
This call to method "T1.m(_)" cannot typecheck.
Argument 1 has type "T1".
That is not a subtype of "T0[T1]" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-.m(this)
""", List.of("""
T0[X]:{ }
T1:T0[T0[T1]]{ .m(a: T0[T1]): T1 -> this.m(this) }
"""));}
@Test void stringLiteralsWithACommaOrACurlyBrace(){ok(List.of("B:{ .m(s: base.Str): B -> this } A:{ .m(b: B): B -> b.m(\"a, b\").m(\"{\").m(`c, d`) }"));}
@Test void expansiveSupertypeArgument(){ok(List.of("""
T0[X]:{ }
T1:T0[T0[T1]]{ .m(a: T0[T0[T1]]): T1 -> this.m(this) }
"""));}
@Test void expansiveSupertypeResultNotASubtype(){fail("""
002| T1:T0[T0[T1]]{ .m: T0[T1] -> this }
   |                --------------^^^^

While inspecting parameter "this" > ".m" line 2
The body of method ".m" of type declaration "T1" is an expression returning "T1".
Parameter "this" has type "T1" instead of a subtype of "T0[T1]".

See inferred typing context below for how type "T0[T1]" was introduced: (compression indicated by `-`)
T1:T0[T0[T1]]{.m:T0[T1]->this}
""", List.of("""
T0[X]:{ }
T1:T0[T0[T1]]{ .m: T0[T1] -> this }
"""));}
@Test void expansiveGenericSupertypeArgumentNotASubtype(){fail("""
002| T1[X]:T0[T0[T1[X]]]{ .m(a: T0[T1[X]]): T1[X] -> this.m(this) }
   |                      ---------------------------~~~~^^^~~~~~

While inspecting ".m(_)" line 2
This call to method "T1[_].m(_)" cannot typecheck.
Argument 1 has type "T1[X]".
That is not a subtype of "T0[T1[X]]" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-.m(this)
""", List.of("""
T0[X]:{ }
T1[X]:T0[T0[T1[X]]]{ .m(a: T0[T1[X]]): T1[X] -> this.m(this) }
"""));}
@Test void expansiveGenericSupertypeArgument(){ok(List.of("""
T0[X]:{ }
T1[X]:T0[T0[T1[X]]]{ .m(a: T0[T0[T1[X]]]): T1[X] -> this.m(this) }
"""));}
@Test void growingSupertypeArgumentNotASubtype(){fail("""
002| T1[X]:T0[T1[T1[X]]]{ .m(a: T0[T1[X]]): T1[X] -> this.m(this) }
   |                      ---------------------------~~~~^^^~~~~~

While inspecting ".m(_)" line 2
This call to method "T1[_].m(_)" cannot typecheck.
Argument 1 has type "T1[X]".
That is not a subtype of "T0[T1[X]]" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-.m(this)
""", List.of("""
T0[X]:{ }
T1[X]:T0[T1[T1[X]]]{ .m(a: T0[T1[X]]): T1[X] -> this.m(this) }
"""));}
@Test void growingSupertypeArgument(){ok(List.of("""
T0[X]:{ }
T1[X]:T0[T1[T1[X]]]{ .m(a: T0[T1[T1[X]]]): T1[X] -> this.m(this) }
"""));}
@Test void growingSupertypeResultNotASubtype(){fail("""
002| T1[X]:T0[T1[T1[X]]]{ .m: T0[T1[X]] -> this }
   |                      -----------------^^^^

While inspecting parameter "this" > ".m" line 2
The body of method ".m" of type declaration "T1[_]" is an expression returning "T1[X]".
Parameter "this" has type "T1[X]" instead of a subtype of "T0[T1[X]]".

See inferred typing context below for how type "T0[T1[X]]" was introduced: (compression indicated by `-`)
T1[X:imm]:T0[T1[T1[X]]]{.m:T0[T1[X]]->this}
""", List.of("""
T0[X]:{ }
T1[X]:T0[T1[T1[X]]]{ .m: T0[T1[X]] -> this }
"""));}
@Test void growingSupertypeResult(){ok(List.of("""
T0[X]:{ }
T1[X]:T0[T1[T1[X]]]{ .m: T0[T1[T1[X]]] -> this }
"""));}
@Test void growingSupertypeInfersMethodTypeArgument(){ok(List.of("""
T0[X]:{ .get: X }
T1[X]:T0[T1[T1[X]]]{ .m[Y](a: T0[Y]): Y -> a.get; .k: T1[T1[X]] -> this.m(this) }
"""));}
@Test void growingSupertypeInfersMethodTypeArgumentNotASubtype(){fail("""
002| T1[X]:T0[T1[T1[X]]]{ .m[Y](a: T0[Y]): Y -> a.get; .k: T1[X] -> this.m(this) }
   |                                                   -------------^^^^^^^^^^^^

While inspecting method call ".m(_)" > ".k" line 2
The body of method ".k" of type declaration "T1[_]" is an expression returning "T1[T1[X]]".
Method call "T1[_].m(_)" has type "T1[T1[X]]" instead of a subtype of "T1[X]".

See inferred typing context below for how type "T1[X]" was introduced: (compression indicated by `-`)
T1[X:imm]:T0[T1[T1[X]]]{.m[Y:imm](a:T0[Y]):Y->a.get;.k:T1[X]->this.m[imm,T1[T1[X]]](this)}
""", List.of("""
T0[X]:{ .get: X }
T1[X]:T0[T1[T1[X]]]{ .m[Y](a: T0[Y]): Y -> a.get; .k: T1[X] -> this.m(this) }
"""));}
@Test void receiverLiteralWithUndeterminedTypeArguments(){failWf("""
001| T0[X0,X1]:{ .m2(x: X0): base.Void; .m0: T0[X0, base.Void] -> {}.m0 }
   |                                                              ^^

While inspecting object literal instance of "T0[_,_]"
Type inference concluded that this object literal implements "T0[?,?]",
but it could not infer generic type arguments 1 and 2 for generic type parameters "X0" and "X1" of "T0[_,_]".
""", List.of("""
T0[X0,X1]:{ .m2(x: X0): base.Void; .m0: T0[X0, base.Void] -> {}.m0 }
"""));}
@Test void receiverLiteralCapturingThis(){failWf("""
001| T0[X]:{ .m: T0[base.Void] -> {this}.m }
   |                              ^^^^^^

While inspecting object literal instance of "T0[_]"
Type inference concluded that this object literal implements "T0[?]",
but it could not infer generic type argument 1 for generic type parameter "X" of "T0[_]".
""", List.of("""
T0[X]:{ .m: T0[base.Void] -> {this}.m }
"""));}
@Test void methodTypeParameterOnlyInLiteralResult(){fail("""
002| T1:{ .m[Y]: T1 -> { .k: Z[Y] -> this } }
   |      ---------------~~~~~~~~~~~~^^^^--

While inspecting parameter "this" > ".k" line 2 > ".m" line 2
Method ".k" inside the object literal instance of "iso T1" (line 2)
is implemented with an expression returning "T1".
Parameter "this" has type "T1" instead of a subtype of "Z[Y]".

See inferred typing context below for how type "Z[Y]" was introduced: (compression indicated by `-`)
T1:{.m[Y:imm]:T1->T1{.k:Z[Y]->this}}
""", List.of("""
Z[X]:{ }
T1:{ .m[Y]: T1 -> { .k: Z[Y] -> this } }
"""));}
@Test void freshMethodGenericMustNotCaptureInheritedSiblingGeneric(){ok(List.of("""
A:{ .foo[_AX,X](a:_AX,b:X):A; }
B[X]:A{ .foo(a,b)->this }
User:{ .m(b:B[User]):A -> b.foo[User,A](this,b) }
"""));}
@Test void freshMethodGenericMustKeepInheritedGenericsDistinct(){fail("""
002| B[X]:A{ .foo(a,b)->b }
   |         -----------^

While inspecting parameter "b" > ".foo(_,_)" line 2
The body of method ".foo(_,_)" of type declaration "B[_]" is an expression returning "_BX".
Parameter "b" has type "_BX" instead of a subtype of "_AX".

See inferred typing context below for how type "_AX" was introduced: (compression indicated by `-`)
B[X:imm]:A{.foo[_AX:imm,_BX:imm](a:_AX,b:_BX):_AX->b}
""", List.of("""
A:{ .foo[_AX,X](a:_AX,b:X):_AX; }
B[X]:A{ .foo(a,b)->b }
"""));}
@Test void keptInheritedMethodGenericMustNotBeCapturedByNestedLiteral(){ok(List.of("""
F[T]:{ .k[X](y:X):T; }
Sup:{ .m[X](x:X):F[X]; }
B:Sup{ .m(x)->{ .k(y)->x } }
"""));}
@Test void keptInheritedMethodGenericMustNotBeCapturedByNestedLiteralWrittenGeneric(){ok(List.of("""
F[T]:{ .k[X](y:X):T; }
Sup:{ .m[X](x:X):F[X]; }
B:Sup{ .m[X](x:X):F[X]->{ .k(y)->x } }
"""));}
@Test void keptInheritedMethodGenericMustNotBeShadowedByNestedLiteral(){fail("""
003| B:Sup{ .m(x)->{ .k(y)->x } }
   |        ---------~~~~~~~^--

While inspecting parameter "x" > ".k(_)" line 3 > ".m(_)" line 3
Method ".k(_)" inside the object literal instance of "iso G" (line 3)
is implemented with an expression returning "imm X".
Parameter "x" has type "imm X" instead of a subtype of "_AX".

See inferred typing context below for how type "_AX" was introduced: (compression indicated by `-`)
B:Sup{.m[X:imm](x:X):G->G{.k[_AX:imm](y:_AX):_AX->x}}
""", List.of("""
G:{ .k[X](y:X):X; }
Sup:{ .m[X](x:X):G; }
B:Sup{ .m(x)->{ .k(y)->x } }
"""));}
@Test void freshMethodGenericMustNotCaptureKeptEnclosingGeneric(){ok(List.of("""
F[T]:{ .k[X](y:X):T; }
Sup:{ .m[_AX](x:_AX):F[_AX]; }
B:Sup{ .m(x)->{ .k(y)->x }; .q[X]:Sup->this }
"""));}
@Test void keptInheritedMethodGenericMustNotBeTypeNameInLiteral(){fail("""
002| A:{ .foo:base.Todo->{ ! -> this } }
   |     ------------------~~~~~^^^^--

While inspecting parameter "this" > "!" line 2 > ".foo" line 2
Method "!" inside the object literal instance of "iso base.Todo" (line 2)
is implemented with an expression returning "A".
Parameter "this" has type "A" instead of a subtype of "_AR".

See inferred typing context below for how type "_AR" was introduced: (compression indicated by `-`)
A:{.foo:-.Todo->-.Todo{![_AR:**]:_AR->this}}
""", List.of("""
R:{}
A:{ .foo:base.Todo->{ ! -> this } }
"""));}
@Test void unnamedLiteralThisMisbinding_getsEnclosingLiteralHint(){fail("""
001| Outer: { #: Inner -> Inner: { .foo: base.Void -> this.bar; .bar: base.Void -> base.Void; } }
   |                               -------------------~~~~^^^^^

While inspecting ".foo" line 1 > "#" line 1
This call to method ".bar" cannot typecheck.
Method ".bar" is not declared on type "Outer".
Hint:
The method parameter "this" here has type "Outer".

The method ".bar" is defined in the object literal of type "Inner".
No parameter refers to instances of this literal.
To declare one, use the single quote as in the example below:
  Rectangles: { #(width: Nat, height: Nat): Rectangle -> Rectangle:{'rect
    .area: Nat -> width * height;
    .str: Str -> "area: "+(rect.area.str);
    .withWidth(width': Nat): Rectangle -> this#(width', height);
  }}

Available methods on type "Outer":
-       #:Inner

Compressed relevant code with inferred types: (compression indicated by `-`)
this.bar
""", List.of("""
Outer: { #: Inner -> Inner: { .foo: base.Void -> this.bar; .bar: base.Void -> base.Void; } }
"""));}
@Test void namedEnclosingLiteralThisMisbinding_getsEnclosingLiteralHint(){fail("""
001| Outer: { #: Inner -> Inner:{'self .foo: Innermost -> Innermost: { .a: base.Void -> this.bar; }; .bar: base.Void -> base.Void; } }
   |                                                                   -----------------~~~~^^^^^

While inspecting ".a" line 1 > ".foo" line 1 > "#" line 1
This call to method ".bar" cannot typecheck.
Method ".bar" is not declared on type "Outer".
Hint:
The method parameter "this" here has type "Outer".

The method ".bar" is defined in the object literal of type "Inner"; the parameter referring to its instances is named "self".

Available methods on type "Outer":
-       #:Inner

Compressed relevant code with inferred types: (compression indicated by `-`)
this.bar
""", List.of("""
Outer: { #: Inner -> Inner:{'self .foo: Innermost -> Innermost: { .a: base.Void -> this.bar; }; .bar: base.Void -> base.Void; } }
"""));}
@Test void anonEnclosingLiteralThisMisbinding_hintDoesNotShowFreshName(){fail("""
002| Outer:{ #: G -> { .foo: base.Void -> this.bar; .bar: base.Void -> base.Void; } }
   |                   -------------------~~~~^^^^^

While inspecting ".foo" line 2 > "#" line 2
This call to method ".bar" cannot typecheck.
Method ".bar" is not declared on type "Outer".
Hint:
The method parameter "this" here has type "Outer".

The method ".bar" is defined in the object literal instance of "G".
No parameter refers to instances of this literal.
To declare one, use the single quote as in the example below:
  Rectangles: { #(width: Nat, height: Nat): Rectangle -> Rectangle:{'rect
    .area: Nat -> width * height;
    .str: Str -> "area: "+(rect.area.str);
    .withWidth(width': Nat): Rectangle -> this#(width', height);
  }}

Available methods on type "Outer":
-       #:G

Compressed relevant code with inferred types: (compression indicated by `-`)
this.bar
""", List.of("""
G:{ .foo: base.Void; .bar: base.Void; }
Outer:{ #: G -> { .foo: base.Void -> this.bar; .bar: base.Void -> base.Void; } }
"""));}
@Test void anonReceiverTypeArgBounds_doesNotShowFreshName(){fail("""
002| Outer:{ #: G -> {'self .foo[X:imm]: base.Void -> base.Void; .bar: base.Void -> self.foo[mut Outer]; } }
   |         ----------------------------------------------------~~~~~~~~~~~~~~~~~~~^^^^^^^^^^^^^^^^^^^^--

While inspecting method call ".foo" > ".bar" line 2 > "#" line 2
The call to ".foo" is invalid.
Generic type argument 1 ("mut Outer") does not satisfy the bounds
for generic type parameter "X" in "G.foo".
Here "X" can only use capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
self.foo[imm,mut Outer]
""", List.of("""
G:{ .foo[X:imm]: base.Void; .bar: base.Void; }
Outer:{ #: G -> {'self .foo[X:imm]: base.Void -> base.Void; .bar: base.Void -> self.foo[mut Outer]; } }
"""));}
@Test void anonLiteralAsTypeArgument_doesNotShowFreshName(){fail("""
004| Outer:{ #: G -> {'self .bar -> base.Void; .v -> Boxes#(self) } }
   |         ----------------------------------~~~~~~^^^^^^^^^^^^--

While inspecting method call "#(_)" > ".v" line 4 > "#" line 4
Method ".v" inside the object literal instance of "iso G" (line 4)
is implemented with an expression returning "Box[G]".
Method call "Boxes#(_)" has type "Box[G]" instead of a subtype of "base.Void".

See inferred typing context below for how type "base.Void" was introduced: (compression indicated by `-`)
Outer:{#:G->G{'self .bar:-.Void->-.Void;.v:-.Void->Boxes#[imm,G](self)}}
""", List.of("""
Box[E]:{ .get: E }
Boxes:{ #[E](e: E): Box[E] -> {.get -> e} }
G:{ .bar: base.Void; .v: base.Void; }
Outer:{ #: G -> {'self .bar -> base.Void; .v -> Boxes#(self) } }
"""));}
@Test void tsMiniFail(){fail("""
001| A:{.foo123:A->this.ba}
   |    -----------~~~~^^^^

While inspecting ".foo123" line 1
This call to method ".ba" cannot typecheck.
Method ".ba" is not declared on type "A".

Available methods on type "A":
-       .foo123:A

Compressed relevant code with inferred types: (compression indicated by `-`)
this.ba
""", List.of("""
A:{.foo123:A->this.ba}
"""));}
@Test void emptyLiteralArgumentOfUndeclaredMethod(){fail("""
001| A:{ .m(x: B): B -> x.foo({}); }
   |     ---------------~^^^^^~~-

While inspecting ".m(_)" line 1
This call to method ".foo(_)" cannot typecheck.
Method ".foo(_)" is not declared on type "B".
Type "B" does not have any methods.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.foo({})
""", List.of("""
A:{ .m(x: B): B -> x.foo({}); }
B:{}
"""));}
@Test void typeNotWellKinded_genericInstantiationViolatesBounds(){fail("""
003| User:{ imm .m(a:imm A[mut B]):base.Void; }
   | --------------------^^^^^^^^--------------

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(a:A[mut B]):-.Void}
""", List.of("""
A[X:imm]:{}
B:{}
User:{ imm .m(a:imm A[mut B]):base.Void; }
"""));}

@Test void typeNotWellKinded_secondTypeArgViolatesBoundsInParamType(){fail("""
004| User:{ imm .m(a:imm A[imm B,mut C]):base.Void; }
   | --------------------^^^^^^^^^^^^^^--------------

While inspecting type declaration "User"
The type "A[B,mut C]" is invalid.
Generic type argument 2 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "A[_,_]".
Here "Y" can only use capabilities "iso" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(a:A[B,mut C]):-.Void}
""", List.of("""
A[X:imm,Y:read,iso]:{}
B:{}
C:{}
User:{ imm .m(a:imm A[imm B,mut C]):base.Void; }
"""));}

@Test void typeNotWellKinded_nestedInnerGenericViolatesBounds(){fail("""
004| User:{ imm .m(a:imm A[B[mut C]]):base.Void; }
   | ----------------------^^^^^^^^---------------

While inspecting type declaration "User"
The type "B[mut C]" is invalid.
Generic type argument 1 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "B[_]".
Here "Y" can only use capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(a:A[B[mut C]]):-.Void}
""", List.of("""
A[X:imm]:{}
B[Y:imm]:{}
C:{}
User:{ imm .m(a:imm A[B[mut C]]):base.Void; }
"""));}

@Test void typeNotWellKinded_literalSupertypeViolatesBounds(){fail("""
003| User:A[mut B]{ .foo(b:B):B->b;}
   | -----^^^^^^^^------------------

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capabilities "imm" or "mutH" or "readH".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:A[mut B]{.foo(b:B):B->b}
""", List.of("""
A[X:imm,readH,mutH]:{}
B:{}
User:A[mut B]{ .foo(b:B):B->b;}
"""));}

@Test void typeNotWellKinded_methodReturnTypeViolatesBounds(){fail("""
003| User:{ imm .m(a:imm B):imm A[mut B]; }
   | ---------------------------^^^^^^^^---

While inspecting type declaration "User"
The type "A[mut B]" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(a:B):A[mut B]}
""", List.of("""
A[X:imm]:{}
B:{}
User:{ imm .m(a:imm B):imm A[mut B]; }
"""));}

@Test void typeNotWellKinded_methodTypeArgViolatesBounds_simple(){fail("""
003| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
   |        -----------------------------------^^^^^^^^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 3
The call to ".id(_)" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A.id(_)".
Here "X" can only use capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,mut B](b)
""", List.of("""
A:{ imm .id[X:imm](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
"""));}

@Test void typeNotWellKinded_methodTypeArgSecondParamViolatesBounds(){fail("""
005| User:{ imm .m(a:imm A,b:imm B,c:imm C):base.Void->a.pair[imm B,mut C](b,c); }
   |        -------------------------------------------^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".pair(_,_)" > ".m(_,_,_)" line 5
The call to ".pair(_,_)" is invalid.
Generic type argument 2 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "A.pair(_,_)".
Here "Y" can only use capability "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.pair[imm,B,mut C](b,c)
""", List.of("""

A:{ imm .pair[X:imm,Y:read](x:X,y:Y):base.Void->{} }
B:{}
C:{}
User:{ imm .m(a:imm A,b:imm B,c:imm C):base.Void->a.pair[imm B,mut C](b,c); }
"""));}

@Test void typeNotWellKinded_methodTypeArgNestedViolatesBounds(){fail("""
004| User:{ imm .m(a:imm A,b:imm B[C],c:imm C):base.Void->a.use[B[mut C]](b); }
   |        ----------------------------------------------~~~~~~^^^^^^^^~~~~

While inspecting method call ".use(_)" > ".m(_,_,_)" line 4
The type "B[mut C]" is invalid.
Generic type argument 1 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "B[_]".
Here "Y" can only use capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.use[imm,B[mut C]](b)
""", List.of("""
A:{ imm .use[X:imm](x:X):base.Void->{} }
B[Y:imm]:{}
C:{}
User:{ imm .m(a:imm A,b:imm B[C],c:imm C):base.Void->a.use[B[mut C]](b); }
"""));}

@Test void typeNotWellKinded_literalHeaderUsesTypeParamViolatingBounds(){fail("""
002| User[Y:read]:A[Y]{}
   | -------------^^^^--

While inspecting type declaration "User[_]"
The type "A[Y]" is invalid.
Generic type argument 1 ("Y") does not satisfy the bounds
for generic type parameter "X" in "A[_]".
Here "X" can only use capability "imm".
But generic type argument "Y" can use capabilities "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
User[Y:read]:A[Y]{}
""", List.of("""
A[X:imm]:{}
User[Y:read]:A[Y]{}
"""));}

@Test void typeNotWellKinded_nestedTwiceInnerMostViolatesBounds(){fail("""
004| User:{ imm .m(x:imm A[B[mut C]]):base.Void; }
   | ----------------------^^^^^^^^---------------

While inspecting type declaration "User"
The type "B[mut C]" is invalid.
Generic type argument 1 ("mut C") does not satisfy the bounds
for generic type parameter "Y" in "B[_]".
Here "Y" can only use capability "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
User:{.m(x:A[B[mut C]]):-.Void}
""", List.of("""
A[X:imm]:{}
B[Y:read]:{}
C:{}
User:{ imm .m(x:imm A[B[mut C]]):base.Void; }
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeWithMultipleBounds(){fail("""
003| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
   |        -----------------------------------^^^^^^^^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 3
The call to ".id(_)" is invalid.
Generic type argument 1 ("mut B") does not satisfy the bounds
for generic type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "imm" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,mut B](b)
""", List.of("""
A:{ imm .id[X:imm,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id[mut B](b); }
"""));}


@Test void typeNotWellKinded_methodTypeArgOnTypeInfer(){fail("""
003| User:{ imm .m(a:imm A,b:imm B):base.Void->a.id(b); }
   |        -----------------------------------^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 3
The call to ".id(_)" is invalid.
Generic type argument 1 ("B") does not satisfy the bounds
for generic type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "mut" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,B](b)
""", List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):base.Void->a.id(b); }
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeInfer2(){fail("""
003| User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
   |        --------------------------------^^^^^^^

While inspecting method call ".id(_)" > ".m(_,_)" line 3
The call to ".id(_)" is invalid.
Generic type argument 1 ("B") does not satisfy the bounds
for generic type parameter "X" in "A.id(_)".
Here "X" can only use capabilities "iso" or "mut".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.id[imm,B](b)
""", List.of("""
A:{ imm .id[X:mut,iso](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):read B->a.id(b); }
"""));}

@Test void typeNotWellKinded_typeExpressionViolatesBounds(){fail("""
004|   .break(cell:imm Cell):base.Void ->
005|     Thaw[mut Cell].apply(cell).set(1);
   |     ^^^^^

While inspecting object literal instance of "Thaw[mut Cell]" > ".break(_)" line 4
The type "Thaw[mut Cell]" is invalid.
Generic type argument 1 ("mut Cell") does not satisfy the bounds
for generic type parameter "X" in "Thaw[_]".
Here "X" can only use capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
Thaw[mut Cell]
""", List.of("""
Cell:{ read .get:base.Nat; mut .set(value:base.Nat):base.Void; }
Thaw[X:imm]:{ .apply(x:imm X):X -> x; }
User:{
  .break(cell:imm Cell):base.Void ->
    Thaw[mut Cell].apply(cell).set(1);
}
"""));}

@Test void typeNotWellKinded_methodTypeArgOnTypeInferFromRetType(){ok(List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:imm B):read B->a.id[read B](b); }
"""));}
@Test void typeNotWellKinded_twistToPassInfer(){ok(List.of("""
A:{ imm .id[X:mut,read](x:X):X->x }
B:{}
User:{ imm .m(a:imm A,b:mut B):read B->a.id[read B](b); }
"""));}


@Test void okViaPushToIso_methodImplementationDeadCode_readLiteralHasMutMethod(){ ok(List.of("""
B:{ mut .h:base.Void; }
User:{
  imm .m():read B->read BB:B{
    mut .h:base.Void->base.Void{};
  }
}
"""));}

@Test void okViaPushToIso_methodImplementationDeadCode_immLiteralHasMutMethod(){ ok(List.of("""
B:{ mut .h:base.Void; }
User:{
  imm .m():imm B->imm BB:B{
    mut .h:base.Void->base.Void{};
  }
}
"""));}

@Test void notAffineIso_usedDirectlyTwice_sameCall(){ fail("""
004| User:{ imm .bad(x:iso B):Unit->Use2#(x,x); }
   |        ------------------------------^^~~

While inspecting ".bad(_)" line 4
Iso parameter "x" violates the single-use rule in method "User.bad(_)" (line 4).
It is used directly 2 times.
Iso parameters can be used directly at most once.
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
Use2#(x,x)
""", List.of("""
Unit:{}
B:{}
Use2:{ #(a:iso B,b:iso B):Unit->Unit{} }
User:{ imm .bad(x:iso B):Unit->Use2#(x,x); }
"""));}

@Test void notAffineIso_usedDirectlyAndCaptured_literalArg(){ fail("""
007|   imm .bad(xyz:iso B):Unit->Mix#(xyz, imm KK:K{ imm .k:Unit->UseImm#(xyz); });
   |   -------------------------------^^^^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~----

While inspecting ".bad(_)" line 7
Iso parameter "xyz" violates the single-use rule in method "User.bad(_)" (line 7).
It is used directly and also captured into object literals.
An iso parameter must be either captured, or used directly once (but not both).
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
Mix#(xyz,KK:K{.k:Unit->UseImm#(xyz)})
""", List.of("""
Unit:{}
B:{}
UseImm:{ #(b:imm B):Unit->Unit{} }
K:{ imm .k:Unit; }
Mix:{ #(a:iso B,k:imm K):Unit->Unit{} }
User:{
  imm .bad(xyz:iso B):Unit->Mix#(xyz, imm KK:K{ imm .k:Unit->UseImm#(xyz); });
}
"""));}

@Test void notAffineIso_usedDirectlyAndCaptured_twice_twoLiterals(){ fail("""
008|   imm .bad(x:iso B):Unit->Mix2#(x,
   |                                 ^^
009|     imm K1:K{ imm .k:Unit->UseImm#(x); },

While inspecting ".bad(_)" line 8
Iso parameter "x" violates the single-use rule in method "User.bad(_)" (line 8).
It is used directly and also captured into object literals.
An iso parameter must be either captured, or used directly once (but not both).
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
Mix2#(x,K1:K{.k:Unit->UseImm#(x)},K2:K{.k:Unit->UseImm#(x)})
""", List.of("""

Unit:{}
B:{}
UseImm:{ #(b:imm B):Unit->Unit{} }
K:{ imm .k:Unit; }
Mix2:{ #(a:iso B,k1:imm K,k2:imm K):Unit->Unit{} }
User:{
  imm .bad(x:iso B):Unit->Mix2#(x,
    imm K1:K{ imm .k:Unit->UseImm#(x); },
    imm K2:K{ imm .k:Unit->UseImm#(x); }
  );
}
"""));}
@Test void notAffineIso_implicitParameterUsedDirectlyTwice(){ fail("""
004| User:{ .bad:base.F[iso B,Unit]->{ Use2#(::,::) } }
   |                                   ------^^^~~~

While inspecting "#(_)" line 4 > ".bad" line 4
Iso parameter "::" violates the single-use rule in method "read base.F[iso B,Unit]#(_)" (line 4).
It is used directly 2 times.
Iso parameters can be used directly at most once.
Allowed: capture into object literals as "imm", or use directly once.

Compressed relevant code with inferred types: (compression indicated by `-`)
Use2#(::,::)
""", List.of("""
Unit:{}
B:{}
Use2:{ #(a:iso B,b:iso B):Unit->Unit{} }
User:{ .bad:base.F[iso B,Unit]->{ Use2#(::,::) } }
"""));}
@Test void notAffineIso_destructuredParameterUsedDirectlyTwice(){ fail("""
002| User:{ .bad({.a,.b}:iso B):B->a }
[###]
While inspecting ".bad(_)" line 2
Iso parameter "{.a, .b}" violates the single-use rule in method "User.bad(_)" (line 2).
It is used directly 2 times.
Iso parameters can be used directly at most once.
Allowed: capture into object literals as "imm", or use directly once.
[###]
""", List.of("""
B:{ .a:B->this; .b:B->this; }
User:{ .bad({.a,.b}:iso B):B->a }
"""));}

@Test void methodBodyWrongType_xWrongNominal_shortNames(){ fail("""
004|   imm .m(x:imm A):B->x;
   |   -------------------^^

While inspecting parameter "x" > ".m(_)" line 4
The body of method ".m(_)" of type declaration "User" is an expression returning "A".
Parameter "x" has type "A" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
User:{.m(x:A):B->x}
""", List.of("""
A:{}
B:{}
User:{
  imm .m(x:imm A):B->x;
}
"""));}

@Test void methodBodyWrongType_xWrongNominal_longNames_indent(){ fail("""
004|   imm .veryLongMethodName(veryVeryLongParamName:imm Alpha):Beta->
005|     veryVeryLongParamName;
   |     ^^^^^^^^^^^^^^^^^^^^^^

While inspecting parameter "veryVeryLongParamName" > ".veryLongMethodName(_)" line 4
The body of method ".veryLongMethodName(_)" of type declaration "User" is an expression returning "Alpha".
Parameter "veryVeryLongParamName" has type "Alpha" instead of a subtype of "Beta".

See inferred typing context below for how type "Beta" was introduced: (compression indicated by `-`)
User:{.veryLongMethodName(veryVeryLongParamName:Alpha):Beta->veryVeryLongParamName}
""", List.of("""
Alpha:{}
Beta:{}
User:{
  imm .veryLongMethodName(veryVeryLongParamName:imm Alpha):Beta->
    veryVeryLongParamName;
}
"""));}

@Test void methodBodyWrongType_callWrongType_namedCallee(){ fail("""
005|   imm .m():B->MakeA#({  }    );
   |   ------------^^^^^^^^^^^-----

While inspecting method call "#(_)" > ".m" line 5
The body of method ".m" of type declaration "User" is an expression returning "A".
Method call "MakeA#(_)" has type "A" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
User:{.m:B->MakeA#(-.Void)}
""", List.of("""
A:{}
B:{}
MakeA:{ #(u:base.Void):A->A{} }
User:{
  imm .m():B->MakeA#({  }    );
}
"""));}

@Test void methodBodyWrongType_callWrongType_rcOnly(){ fail("""
004|   imm .m():mut A->MakeA#({  }    );
   |   ----------------^^^^^^^^^^^-----

While inspecting method call "#(_)" > ".m" line 4
The body of method ".m" of type declaration "User" is an expression returning "A".
Method call "MakeA#(_)" has type "A" instead of a subtype of "mut A".

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
User:{.m:mut A->MakeA#(-.Void)}
""", List.of("""
A:{}
MakeA:{ #(u:base.Void):A->A{} }
User:{
  imm .m():mut A->MakeA#({  }    );
}
"""));}

@Test void methodBodyWrongType_callWrongType_rcOnly_nested(){ fail("""
005|   imm .m():Get->mut Get{
006|     mut .get:mut A->MakeA#({});
   |     ----------------^^^^^^^^^-
007|   };

While inspecting method call "#(_)" > ".get" line 6 > ".m" line 5
Method ".get" inside the object literal instance of "iso Get" (line 5)
is implemented with an expression returning "A".
Method call "MakeA#(_)" has type "A" instead of a subtype of "mut A".

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
User:{.m:Get->mut Get{mut .get:mut A->MakeA#(-.Void)}}
""", List.of("""
A:{}
MakeA:{ #(u:base.Void):A->A{} }
Get:{ mut .get:mut A; }
User:{
  imm .m():Get->mut Get{
    mut .get:mut A->MakeA#({});
  };
}
"""));}

@Test void methodBodyWrongType_inferredContextShowsInferredGenericInstantiation(){fail("""
007|   imm .m():Car->Apply#(Person,{_->Foo});
   |   -----------------------------~~~^^^^-

While inspecting object literal instance of "Foo" > "#(_)" line 7 > ".m" line 7
Method "#(_)" inside the object literal instance of "iso F[Person,Car]" (line 7)
is implemented with an expression returning "iso Foo".
Object literal is of type "Foo" instead of a subtype of "Car".

See inferred typing context below for how type "Car" was introduced: (compression indicated by `-`)
User:{.m:Car->Apply#(Person,F[Person,Car]{#(Person):Car->Foo})}
""", List.of("""
Person:{}
Car:{}
Foo:{}
F[A:imm,B:imm]:{ #(a:imm A):B; }
Apply:{ #(p:imm Person, f:imm F[Person,Car]):Car->f#(p); }
User:{
  imm .m():Car->Apply#(Person,{_->Foo});
}
"""));}
@Test void methodBodyWrongType_callWrongType_nestedCall(){ fail("""
006|   imm .m():B->Wrap#(Mk#({}));
   |   ------------^^^^^^^^^^^^--

While inspecting method call "#(_)" > ".m" line 6
The body of method ".m" of type declaration "User" is an expression returning "A".
Method call "Wrap#(_)" has type "A" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
User:{.m:B->Wrap#(Mk#(-.Void))}
""", List.of("""
A:{}
B:{}
Mk:{ #(u:base.Void):A->A{} }
Wrap:{ #(a:A):A->a }
User:{
  imm .m():B->Wrap#(Mk#({}));
}
"""));}

@Test void methodBodyWrongType_literalWrongType_namedLiteral(){ fail("""
004|   imm .m():B->imm AA:A{};
   |   ----------------^^^^^^

While inspecting object literal "AA" > ".m" line 4
The body of method ".m" of type declaration "User" is an expression returning "iso AA".
Object literal is of type "iso AA" instead of a subtype of "B".

See inferred typing context below for how type "B" was introduced: (compression indicated by `-`)
User:{.m:B->AA:A{}}
""", List.of("""
A:{}
B:{}
User:{
  imm .m():B->imm AA:A{};
}
"""));}
@Test void methodBodyWrongType_xWeakenedCapability_dueToCapture(){fail("""
004|   read .m(loooooong:mut A):mut A->
005|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > ".get" line 5 > ".m(_)" line 4
Method ".get" inside the object literal instance of "read Get" (line 5)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capture adaptation trace:
"mut A" --setToRead(line 5)--> "read A".

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
User:{read .m(loooooong:mut A):mut A->read Get{read .get:mut A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: mut A; }
User:{
  read .m(loooooong:mut A):mut A->
    read Get{ loooooong };
}
"""));}
@Test void methodBodyWrongType_xWeakenedCapability_dueToCapture2(){fail("""
004|   read .m(loooooong:mut A):read Get->
005|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > ".get" line 5 > ".m(_)" line 4
Method ".get" inside the object literal instance of "read Get" (line 5)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capture adaptation trace:
"mut A" --setToRead(line 5)--> "read A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
User:{read .m(loooooong:mut A):read Get->read Get{read .get:iso A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: iso A; }
User:{
  read .m(loooooong:mut A):read Get->
    read Get{ loooooong };
}
"""));}
@Test void regressionBadError(){fail("""
004|   read .m(loooooong:mut A):mut A->
005|     read Get{ loooooong };
   |               ^^^^^^^^^

While inspecting parameter "loooooong" > ".get" line 5 > ".m(_)" line 4
Method ".get" inside the object literal instance of "read Get" (line 5)
is implemented with an expression returning "read A".
Parameter "loooooong" has type "read A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capture adaptation trace:
"mut A" --setToRead(line 5)--> "read A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
User:{read .m(loooooong:mut A):mut A->read Get{read .get:iso A->loooooong}}
""", List.of("""
A:{}
Get:{ read .get: iso A; }
User:{
  read .m(loooooong:mut A):mut A->
    read Get{ loooooong };
}
"""));}

@Test void methodBodyWrongType_xWeakenedCapability_dueToCapture_chain(){fail("""
005|   read .m(loooooong:mut A):mut A->
006|     read Wrap{ mut Get{ loooooong } };
   |                ---------^^^^^^^^^--

While inspecting parameter "loooooong" > ".get" line 6 > ".wrap" line 6 > ".m(_)" line 5
Method ".get" inside the object literal instance of "mut Get" (line 6)
is implemented with an expression returning "A".
Parameter "loooooong" has type "imm A" instead of a subtype of "iso A".
Note: the declared type "mut A" also does not satisfy the requirement.
Capture adaptation trace:
"mut A" --setToRead(line 6)--> "read A" --strengthenToImm(line 6)--> "A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
User:{read .m(loooooong:mut A):mut A->read Wrap{read .wrap:Get->mut Get{.get:iso A->loooooong}}}
""", List.of("""
A:{}
Get:{ imm .get: iso A; }
Wrap:{ read .wrap: imm Get; }
User:{
  read .m(loooooong:mut A):mut A->
    read Wrap{ mut Get{ loooooong } };
}
"""));
}

@Test void drop_capFree(){fail("""
003| Foo:{#(a:A):G->{a}}
   |      -----------^^

While inspecting parameter "a" > "#" line 3 > "#(_)" line 3
Object literal instance of "iso G" implements "base.CaptureFree".
Thus parameter "a" (line 3) cannot be captured in this scope.

Compressed relevant code with inferred types: (compression indicated by `-`)
a
""", List.of("""
A:{}
G:base.CaptureFree{ #:A; }
Foo:{#(a:A):G->{a}}
""")); }


@Test void drop(){fail("""
007|   read .m(loooooong:mut A):mut A->Do2[mut A]#(
008|     Capture#({#():base.Void->Ignore#(loooooong)}),
   |               -----------------------^^^^^^^^^^
009|     loooooong
010|   );

While inspecting parameter "loooooong" > "#" line 8 > ".m(_)" line 7
Parameter "loooooong" has type "mut A".
Parameter "loooooong" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "G" (line 8).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
loooooong
""", List.of("""
A:{}
G:{ #(): base.Void; }
Ignore:{ #(x: read A): base.Void->{}; }
Capture:{#(g: G): base.Void->{}; }
Do2[X:imm,mut,read]: { #(v:base.Void, x:X):X->x; }
User:{
  read .m(loooooong:mut A):mut A->Do2[mut A]#(
    Capture#({#():base.Void->Ignore#(loooooong)}),
    loooooong
  );
}
"""));}

@Test void drop_hygienicMutH(){fail("""
007|   read .m(loooooong:mutH A):mutH A->Do2H[mutH A]#(
008|     Capture#({#():base.Void->Ignore#(loooooong)}),
   |               -----------------------^^^^^^^^^^
009|     loooooong
010|   );

While inspecting parameter "loooooong" > "#" line 8 > ".m(_)" line 7
Parameter "loooooong" has type "mutH A".
The type of parameter "loooooong" is hygienic (readH or mutH)
and thus it cannot be captured in the object literal instance of "G" (line 8).

Compressed relevant code with inferred types: (compression indicated by `-`)
loooooong
""", List.of("""
A:{}
G:{ #(): base.Void; }
Ignore:{ #(x: mutH A): base.Void->{}; }
Capture:{ #(g: G): base.Void->{}; }
Do2H[X:imm,mut,read,readH,mutH]: { #(v:base.Void, x:X):X->x; }
User:{
  read .m(loooooong:mutH A):mutH A->Do2H[mutH A]#(
    Capture#({#():base.Void->Ignore#(loooooong)}),
    loooooong
  );
}
""")); }

@Test void drop_hygienicMutH2(){fail("""
005|   read .m(loooooong:mutH A):imm G->
006|     {#():base.Void->IgnoreH#(loooooong)};
   |      ------------------------^^^^^^^^^^

While inspecting parameter "loooooong" > "#" line 6 > ".m(_)" line 5
Parameter "loooooong" has type "mutH A".
The type of parameter "loooooong" is hygienic (readH or mutH)
and thus it cannot be captured in the object literal instance of "G" (line 6).

Compressed relevant code with inferred types: (compression indicated by `-`)
loooooong
""", List.of("""
A:{}
G:{ #(): base.Void; }
IgnoreH:{ #(x: mutH A): base.Void->{}; }
User:{
  read .m(loooooong:mutH A):imm G->
    {#():base.Void->IgnoreH#(loooooong)};
}
""")); }
@Test void shouldPassViaInference(){ok(List.of("""
Bar:{}
Beer[X:imm,mut,read]:{ read .bar: Bar; }
Foo:{ read .m: Bar; }
User:{
  read .m[X:imm,mut,read](webeer:Beer[X]):read Foo->
    read Foo{ webeer.bar() };
}
""")); }

@Test void drop_ftv_notPropagatedIntoExplicitFoo(){failWf("""
005|       read Foo:{ read .m:Bar -> beer.bar() };
   |                                 ^^^^^

While inspecting parameter "beer"
Parameter "beer" has type "Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Hint: funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  User:{
    read .m[X:imm,mut,read](beer:Beer[X]):read Foo->
      read Foo:{ read .m:Bar -> beer.bar() };
  }
""")); }
@Test void drop_ftv_typeVariableNotPropagatedIntoExplicitFoo(){failWf("""
004|       read Foo:{ read .m:Bar -> x };
   |                                 ^

While inspecting parameter "x"
Parameter "x" has type "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Hint: funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  User:{
    read .m[X:imm,mut,read](x:X):read Foo->
      read Foo:{ read .m:Bar -> x };
  }
"""));}
@Test void drop_ftv_notPropagatedTypeReachesInferredTypeArgument(){failWf("""
006|       read Foo:{ read .m:Bar -> Id#beer };
   |                                    ^^^^

While inspecting parameter "beer"
Parameter "beer" has type "Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Hint: funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  Id:{ #[Y:imm,mut,read](y:Y):Bar -> Bar }
  User:{
    read .m[X:imm,mut,read](beer:Beer[X]):read Foo->
      read Foo:{ read .m:Bar -> Id#beer };
  }
"""));}
@Test void drop_ftv_notPropagatedTypeReachesNestedLiteral(){failWf("""
007|       read Foo:{ read .m:Bar -> Do#{ beer.bar } };
   |                                      ^^^^^

While inspecting parameter "beer"
Parameter "beer" has type "Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares none.
Hint: funnel "X" into "Foo" by writing "Foo[X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  Run:{ read #: Bar }
  Do:{ #(r: read Run): Bar -> Bar }
  User:{
    read .m[X:imm,mut,read](beer:Beer[X]):read Foo->
      read Foo:{ read .m:Bar -> Do#{ beer.bar } };
  }
"""));}
@Test void drop_ftv_notPropagatedIntoFooDeclaringOther(){failWf("""
[###]
Parameter "beer" has type "Beer[X]", using the generic type parameter "X".
Generic type parameter "X" is not in scope inside the type declaration "Foo".
A type declaration only sees the generic type parameters it declares itself; here "Foo" declares "Z".
Hint: funnel "X" into "Foo" by writing "Foo[Z:..,X:..]", restating the bounds of "X".
""", List.of("""
  Bar:{}
  Beer[X:imm,mut,read]:{ read .bar: Bar; }
  User:{
    read .m[X:imm,mut,read,Z](beer:Beer[X]):read Foo[Z]->
      read Foo[Z]:{ read .m:Bar -> beer.bar() };
  }
"""));}

@Test void drop_hygienicsAllowedByTypeParam(){fail("""
002|   read .m[X:imm,mut,read,readH,mutH](beer:X):G[X]->
003|     G[X:imm,mut,read,readH,mutH]:{ read .get: X->beer; }
   |                                    --------------^^^^^

While inspecting parameter "beer" > ".get" line 3 > ".m(_)" line 2
Parameter "beer" has type "X".
The type of parameter "beer" can be instantiated with hygienics (readH or mutH)
and thus it cannot be captured in the object literal "G[_]" (line 3).

Compressed relevant code with inferred types: (compression indicated by `-`)
beer
""", List.of("""
User:{
  read .m[X:imm,mut,read,readH,mutH](beer:X):G[X]->
    G[X:imm,mut,read,readH,mutH]:{ read .get: X->beer; }
}
""")); }

@Test void receiverIsTypeParamDeepInsideCalls(){fail("""
002| User:{ .m[X:*](x: X): X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
   |        ----------------------------------------~^^^^^----

While inspecting ".m(_)" line 2
This call to method ".foo" cannot typecheck.
The receiver is of type "X". This is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
-#[imm,X](Id#[imm,X](Id#[imm,X](Id#[imm,X](Id#[imm,X](x.foo)))))
""", List.of("""
Id:{ #[T:*](t: T): T -> t }
User:{ .m[X:*](x: X): X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
"""));}
@Test void receiverIsReadTypeParamDeepInsideCalls(){fail("""
004| User:Sup[Box[User]]{ .m[X:*](x: read X): read X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
   |                      --------------------------------------------------~^^^^^----

While inspecting ".m(_)" line 4
This call to method ".foo" cannot typecheck.
The receiver is of type "read X". This is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

See inferred typing context below for how type "read X" was introduced: (compression indicated by `-`)
-#[imm,read X](Id#[imm,read X](Id#[imm,read X](Id#[imm,read X](Id#[imm,read X](x.foo)))))
""", List.of("""
Id:{ #[T:*](t: T): T -> t }
Box[T:*]:{}
Sup[T:*]:{}
User:Sup[Box[User]]{ .m[X:*](x: read X): read X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
"""));}
@Test void receiverIsReadImmTypeParamDeepInsideCalls(){fail("""
002| User:{ .m[X:*](x: read/imm X): read/imm X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
   |        ----------------------------------------------------------~^^^^^----

While inspecting ".m(_)" line 2
This call to method ".foo" cannot typecheck.
The receiver is of type "read/imm X". This is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

See inferred typing context below for how type "read/imm X" was introduced: (compression indicated by `-`)
-#[imm,read/imm X](Id#[imm,read/imm X](Id#[imm,read/imm X](Id#[imm,read/imm X](Id#[imm,read/imm X](x.foo)))))
""", List.of("""
Id:{ #[T:*](t: T): T -> t }
User:{ .m[X:*](x: read/imm X): read/imm X -> Id#(Id#(Id#(Id#(Id#(x.foo))))) }
"""));}
@Test void inferredTypeArgumentWithAnUnknownPartAndATypeParameter(){ok(List.of("""
Pair[A:*,B:*]:{}
Mk:{ #[A:*,B:*](a: A): Pair[A,B] -> {} }
Ig:{ #[T:*](t: T): base.Void -> base.Void }
User:{ .m[X:*](x: X): base.Void -> Ig#(Mk#(x)) }
"""));}
@Test void receiverIsTypeParam(){fail("""
002|   .m[X:**](x:X):X->x.foo;
   |   -----------------~^^^^^

While inspecting ".m(_)" line 2
This call to method ".foo" cannot typecheck.
The receiver is of type "X". This is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
User:{.m[X:**](x:X):X->x.foo}
""", List.of("""
User:{
  .m[X:**](x:X):X->x.foo;
}
""")); }
//-----------
@Test void methodOverrideSignatureMismatchGenericBounds(){ failExt("""
In file: [###].fear

003| Current:Parent2{ imm .id[X:imm,read](x:imm X):base.Void; }
   |                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Current"
Invalid method implementation for "Current.id(_)".
The local declaration uses different capability bounds than the supertypes for generic type parameter 1 of ".id(_)".
Local: "X:imm,read".
From supertypes: "-:imm".
The parameter name may differ; only the position matters.
Change the local bounds to match the supertypes, or adjust the supertypes.
Error 7 WellFormedness
""", List.of("""
P:{}
Parent2:{ imm .id[X:imm](x:imm X):base.Void; }
Current:Parent2{ imm .id[X:imm,read](x:imm X):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchGenericBoundsArity(){ failExt("""
In file: [###].fear

003| Sub:Sup{ imm .f[X:imm,Y:imm](x:imm X):base.Void; }
   |          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "Sub"
Invalid method implementation for "Sub.f(_)".
The method ".f(_)" declares 2 generic type parameters, but supertypes declare 1.
Local declaration: "[X:imm, Y:imm]".
From supertypes: "[-:imm]".
Change the local number of generic type parameters to 1, or adjust the supertypes.
Error 7 WellFormedness
""", List.of("""
P:{}
Sup:{ imm .f[X:imm](x:imm X):base.Void; }
Sub:Sup{ imm .f[X:imm,Y:imm](x:imm X):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchContravariance(){ fail("""
004| Current:Parent{ imm .g(x:imm P):base.Void; }
   | ----------------^^^^^^^^^^^^^^^^^^^^^^^^^---

While inspecting type declaration "Current"
Invalid method signature overriding for "Current.g(_)".
The method ".g(_)" accepts parameter 1 of type "imm P".
But "Parent.g(_)" requires "read P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.

Compressed relevant code with inferred types: (compression indicated by `-`)
Current:Parent{.g(x:P):-.Void}
""", List.of("""

P:{}
Parent:{ imm .g(x:read P):base.Void; }
Current:Parent{ imm .g(x:imm P):base.Void; }
"""));}

@Test void methodOverrideSignatureMismatchCovariance(){ fail("""
003| Sub:Sup{ imm .h():read P; }
   | ---------^^^^^^^^^^^^^^^---

While inspecting type declaration "Sub"
Invalid method signature overriding for "Sub.h".
The method ".h" returns type "read P".
But "Sup.h" returns type "imm P".
An overriding method can refine the types of its parameters and result, but not their reference capabilities.

Compressed relevant code with inferred types: (compression indicated by `-`)
Sub:Sup{.h:read P}
""", List.of("""
P:{}
Sup:{ imm .h():imm P; }
Sub:Sup{ imm .h():read P; }
""")); }

@Test void callableMethodStillAbstract_missingRequiredMethod_anonLiteral(){ fail("""
006|   imm .m():Sup->Sup{ imm .h:base.Void->base.Void{} }
   |   --------------^^^^--------------------------------

While inspecting object literal instance of "iso Sup" > ".m" line 6
This object literal is missing a required method.
Missing: "imm .k".
Required by: "Sup".
Hint: add an implementation for ".k" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso Sup{.h:-.Void->-.Void}
""", List.of("""
Sup:{
  imm .h:base.Void;
  imm .k:base.Void;
}
User:{
  imm .m():Sup->Sup{ imm .h:base.Void->base.Void{} }
}
"""));}

@Test void callableMethodStillAbstract_missingRequiredMethod_namedLiteral(){ fail("""
006|   imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{} }
   |   --------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal "iso Bad" > ".m" line 6
This object literal is missing a required method.
Missing: "imm .k".
Required by: "Sup".
Hint: add an implementation for ".k" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso Bad:Sup{.h:-.Void->-.Void}
""", List.of("""
Sup:{
  imm .h:base.Void;
  imm .k:base.Void;
}
User:{
  imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{} }
}
"""));}


@Test void methodNotDeclared_noSuchName_typeHasNoMethods(){fail("""
003|   read .m(e:Empty):base.Void->
004|     e.nope();
   |     -^^^^^^

While inspecting ".m(_)" line 3
This call to method ".nope" cannot typecheck.
Method ".nope" is not declared on type "Empty".
Type "Empty" does not have any methods.

Compressed relevant code with inferred types: (compression indicated by `-`)
e.nope
""", List.of("""
Empty:{}
User:{
  read .m(e:Empty):base.Void->
    e.nope();
}
""")); }

@Test void methodNotDeclared_noSuchName_didYouMean(){fail("""
007|   read .m(o:Ops):base.Void->
008|     read Runner{ o.sise() };
   |                  ~^^^^^^-

While inspecting ".run" line 8 > ".m(_)" line 7
This call to method ".sise" cannot typecheck.
Method ".sise" is not declared on type "Ops".
Did you mean ".size" ?

Available methods on type "Ops":
-  read .sign:base.Void
-  read .size:base.Void

Compressed relevant code with inferred types: (compression indicated by `-`)
o.sise
""", List.of("""
Ops:{
  read .size: base.Void->{};
  read .sign: base.Void->{};
}
Runner:{ read .run: base.Void; }
User:{
  read .m(o:Ops):base.Void->
    read Runner{ o.sise() };
}
""")); }
@Test void methodNotDeclared_noSuchName_listAvailable(){fail("""
007|   read .m(o:Ops):base.Void->
008|     o.xyzzy();
   |     -^^^^^^^

While inspecting ".m(_)" line 7
This call to method ".xyzzy" cannot typecheck.
Method ".xyzzy" is not declared on type "Ops".

Available methods on type "Ops":
-  read .alpha:base.Void
-  read .beta:base.Void
-  read .gamma:base.Void

Compressed relevant code with inferred types: (compression indicated by `-`)
o.xyzzy
""", List.of("""
Ops:{
  read .alpha: base.Void->{};
  read .beta: base.Void->{};
  read .gamma: base.Void->{};
}
User:{
  read .m(o:Ops):base.Void->
    o.xyzzy();
}
""")); }

@Test void methodNotDeclared_noSuchName_listAvailable_useVoid(){fail("""
008|   read .m(o:Ops):Woid->
009|     o.xyzzy();
   |     -^^^^^^^

While inspecting ".m(_)" line 8
This call to method ".xyzzy" cannot typecheck.
Method ".xyzzy" is not declared on type "Ops".

Available methods on type "Ops":
-  read .alpha:Woid
-  read .beta:Woid
-  read .gamma:Woid

Compressed relevant code with inferred types: (compression indicated by `-`)
o.xyzzy
""", List.of("""
use base.Void as Woid;
Ops:{
  read .alpha: Woid->{};
  read .beta:  Woid->{};
  read .gamma: Woid->{};
}
User:{
  read .m(o:Ops):Woid->
    o.xyzzy();
}
""")); }


@Test void methodNotDeclared_wrongArity_listsAvailableArities(){fail("""
007|   read .m(m:Mixer, a:A):A->
008|     m.mix(a, a, a);
   |     -^^^^^--------

While inspecting ".m(_,_)" line 7
This call to method ".mix(_,_,_)" cannot typecheck.
There are methods ".mix(_)" and ".mix(_,_)" on type "Mixer",
but with a different number of arguments.
This call supplies 3, but available methods take 1 or 2.

Compressed relevant code with inferred types: (compression indicated by `-`)
m.mix(a,a,a)
""", List.of("""
A:{}
Mixer:{
  read .mix(x:A):A->x;
  read .mix(x:A, y:A):A->x;
}
User:{
  read .m(m:Mixer, a:A):A->
    m.mix(a, a, a);
}
""")); }
@Test void methodNotDeclared_wrongReceiverRc_mutNeedsMutButOnlyReadExists(){fail("""
006|   mut .m(z:mut Z, a:A):A->
007|     z.zap[mut](a);
   |     -^^^^^-------

While inspecting ".m(_,_)" line 6
This call to method ".zap(_)" cannot typecheck.
".zap(_)" exists on type "Z", but not with the requested capability.
This call requires the existence of a "mut" method.
Available capabilities for this method: "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
z.zap[mut](a)
""", List.of("""
A:{}
Z:{
  read .zap(x:A):A->x;
}
User:{
  mut .m(z:mut Z, a:A):A->
    z.zap[mut](a);
}
""")); }
@Test void methodNotDeclared_wrongReceiverRc_onObjectLiteralInstance(){fail("""
002| U:{ .u: base.Void -> mut A{ read .m: base.Void -> base.Void; mut .k: base.Void -> base.Void }.k[read] }
   |     ---------------------~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~^^^~~~~~

While inspecting ".u" line 2
This call to method ".k" cannot typecheck.
".k" exists on object literal instance of "A", but not with the requested capability.
This call requires the existence of a "read" method.
Available capabilities for this method: "mut".

Compressed relevant code with inferred types: (compression indicated by `-`)
mut A{read .m:-.Void->-.Void;mut .k:-.Void->-.Void}.k[read]
""", List.of("""
A:{ read .m: base.Void }
U:{ .u: base.Void -> mut A{ read .m: base.Void -> base.Void; mut .k: base.Void -> base.Void }.k[read] }
""")); }
@Test void methodNotDeclared_wrongReceiverRc_twoOtherCapabilitiesExist(){fail("""
002| User:{ #(a:read A):A->a.m[read] }
   |        ---------------~^^^~~~~~

While inspecting "#(_)" line 2
This call to method ".m" cannot typecheck.
".m" exists on type "A", but not with the requested capability.
This call requires the existence of a "read" method.
Available capabilities for this method: "imm" and "mut".

Compressed relevant code with inferred types: (compression indicated by `-`)
a.m[read]
""", List.of("""
A:{ mut .m:A; imm .m:A; }
User:{ #(a:read A):A->a.m[read] }
""")); }
@Test void methodTArgsArityError_oneLessThanNeeded(){fail("""
007|   read .m(p:Pairer,a:mut A,b:mut B):mut A->
008|     p.pair[mut A](a,b);
   |     -^^^^^^-----------

While inspecting ".m(_,_,_)" line 7
This call to method "read Pairer.pair(_,_)" cannot typecheck.
Wrong number of generic type arguments for ".pair(_,_)".
This method expects 2 generic type arguments: "X" and "Y"; but this call provides 1 generic type argument.

Compressed relevant code with inferred types: (compression indicated by `-`)
p.pair[read,mut A](a,b)
""", List.of("""
A:{}
B:{}
Pairer:{
  read .pair[X:imm,mut,read,Y:imm,mut,read](x:X,y:Y):X->x;
}
User:{
  read .m(p:Pairer,a:mut A,b:mut B):mut A->
    p.pair[mut A](a,b);
}
"""));}

@Test void methodTArgsArityError_twoMoreThanNeeded(){fail("""
009|   read .m(i:Id,a:mut A):mut A->
010|     i.id[mut A,mut B,mut C](a);
   |     -^^^^---------------------

While inspecting ".m(_,_)" line 9
This call to method "read Id.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
This method expects 1 generic type argument: "X"; but this call provides 3 generic type arguments.

Compressed relevant code with inferred types: (compression indicated by `-`)
i.id[read,mut A,mut B,mut C](a)
""", List.of("""

A:{}
B:{}
C:{}
Id:{
  read .id[X:imm,mut,read](x:X):X->x;
}
User:{
  read .m(i:Id,a:mut A):mut A->
    i.id[mut A,mut B,mut C](a);
}
"""));}

@Test void rcvBlocksCall(){fail("""
004|   read .m(a:A):A->
005|     this.zap(a);
   |     ----^^^^^--

While inspecting ".m(_)" line 4
This call to method "mut User.zap(_)" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.zap[mut](a)
""", List.of("""
A:{}
User:{
  mut .zap(x:A):A->x;
  read .m(a:A):A->
    this.zap(a);
}
""")); }
@Test void operatorArgMismatch_getsNoPrecedenceHint(){fail("""
005|   .go:Plus->this + this.other;
   |   ----------~~~~~^~~~~~~-----

While inspecting ".go" line 5
This call to method "Plus+(_)" cannot typecheck.
Argument 1 has type "Plus".
That is not a subtype of "A" (the type required by the method signature).
Hint: Fearless has no operator precedence, so an expression like "a.get + b.get" parses as "(a.get + b).get", not "a.get + (b.get)". If this argument needed a method applied to it first, wrap it in parentheses.

Compressed relevant code with inferred types: (compression indicated by `-`)
-+(this)
""", List.of("""
A:{}
Plus:{
  +(x:A):Plus->this;
  .other:A->A{};
  .go:Plus->this + this.other;
}
"""));}
@Test void hopelessArg_wrongNominal_suppressesPromotionsAndReason(){fail("""
005|   .f(aaaa:mut B):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~^^~~~~~~~~~~~~~-

While inspecting ".foo" line 5 > ".f(_)" line 5
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read B".
That is not a subtype of "mut A" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-#(AsRead#(aaaa))
""", List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read B):read B->x }
A:{
  .f(aaaa:mut B):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));}
@Test void hopelessArg_wrongNominal_mutHReceiver_showsDeclaredType(){fail("""
005|   .f(n:mutH Need, b:B):B->n#b
   |   ------------------------~^^

While inspecting ".f(_,_)" line 5
This call to method "mut Need#(_)" cannot typecheck.
Argument 1 has type "B".
That is not a subtype of "mut A" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-#[mut](b)
""", List.of("""
A:{}
B:{}
Need:{ mut #(a:mut A):B->B }
User:{
  .f(n:mutH Need, b:B):B->n#b
}
"""));}

@Test void hopelessArg_calls_pArgHasType_baselineConsistent(){fail("""
005|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~^^~~~~~~~~~~~~~-

While inspecting ".foo" line 5 > ".f(_)" line 5
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Method call "AsRead#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa))}}
""", List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read A):read A->x }
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));}

@Test void noVar2Fail_viewpointAdaptation_reasonShown(){fail("""
005|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,mut A](aaaa);}
   |                                    -------------~~~~^^~~~~~~~~~~~~~~~~

While inspecting ".foo" line 5 > ".f(_)" line 5
This call to method "Skip#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Parameter "aaaa" has type "read A" instead of a subtype of "mut A".
Note: the declared type "mut A" would instead be a valid subtype.
Capture adaptation trace:
"mut A" --setToRead(line 5)--> "read A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,mut A](aaaa)}}
""", List.of("""

Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,mut A](aaaa);}
}
"""));}

@Test void deepCall_usingRCfiltering(){ok(List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}
}
"""));}

@Test void argFromGenericCall_boundForcesRead_inferenceHintBadBounds(){fail("""
006|   .f(aaaa:mut A):B->
007|     Need#(IdRO#(aaaa));
   |           ^^^^^^^^^^^

While inspecting method call "#(_)" > ".f(_)" line 6
The call to "#(_)" is invalid.
Generic type argument 1 ("mut A") does not satisfy the bounds
for generic type parameter "X" in "IdRO#(_)".
Here "X" can only use capabilities "imm" or "read".

Compressed relevant code with inferred types: (compression indicated by `-`)
IdRO#[imm,mut A](aaaa)
""", List.of("""

B:{}
Need:{ #(a:mut A):B->B{} }
IdRO:{ #[X:imm,read](x:X):X->x }
A:{
  .f(aaaa:mut A):B->
    Need#(IdRO#(aaaa));
}
"""));}

@Test void argFromGenericCall_boundForcesRead_inferenceHint(){fail("""
005|   .f(aaaa:mut A):B->
006|     Need#(IdRO#[read A](aaaa));
   |     ----^^-------------------

While inspecting ".f(_)" line 5
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Method call "IdRO#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):B->Need#(IdRO#[imm,read A](aaaa))}
""", List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
IdRO:{ #[X:imm,read](x:X):X->x }
A:{
  .f(aaaa:mut A):B->
    Need#(IdRO#[read A](aaaa));
}
"""));}

@Test void argFromObjectLiteral_defaultImm_hintToAnnotate(){fail("""
005|   .f:B->
006|     Need#(read A{});
   |     ----^^-------

While inspecting ".f" line 5
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Object literal is of type "read A" instead of a subtype of "mut A".
Hint: write "mut A" if you need a "mut" object literal.

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
User:{.f:B->Need#(read A)}
""", List.of("""
B:{}
Need:{ #(a:mut A):B->B{} }
A:{ mut .foo:A}
User:{
  .f:B->
    Need#(read A{});
}
"""));}

@Test void promotionsDisagree_mergesIdenticalBlocks_readH_mutH(){fail("""
003|   .caller(x:readH A, y:mutH A):A->this.f(x,y);
   |   --------------------------------~~~~^^^~~~~

While inspecting ".caller(_,_)" line 3
This call to method ".f(_,_)" cannot typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Parameter "x" has type "readH A" instead of a subtype of "read A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow mutH receiver, Allow mutH argument 2
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 fails:    Allow readH arguments, Allow mutH argument 1
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(x,y)
""", List.of("""
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void promotionsDisagree_dontOverMergeAcrossDifferentArgs_mutH_mutH(){fail("""
003|   .caller(x:mutH A, y:mutH A):A->this.f(x,y);
   |   -------------------------------~~~~^^^~~~~

While inspecting ".caller(_,_)" line 3
This call to method ".f(_,_)" cannot typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "mutH A" and is compatible with: Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Parameter "x" has type "mutH A" instead of a subtype of "mut A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow readH arguments, Allow mutH receiver, Allow mutH argument 2
  Parameter "x" has type "mutH A" instead of a subtype of "iso A".
- Argument 2 fails:    Allow mutH argument 1
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(x,y)
""", List.of("""
A:{
  .f(a:mut A, b:mut A):A->this;
  .caller(x:mutH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void tsOkIndirect(){ok(List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo123;}
"""));}

@Test void tsOkIndirectFail1(){fail("""
001| A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
   |                            --------~~~~^^^^^^^^

While inspecting ".bar" line 1
This call to method ".foO123" cannot typecheck.
Method ".foO123" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
-       .bar:A
-   mut .bob(A):A
-       .foo123:A

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foO123
""", List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foO123; mut .bob(a:A):A}
"""));}

@Test void tsOkIndirectFail2(){fail("""
001| A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
   |                            --------~~~~^^^^^^^

While inspecting ".bar" line 1
This call to method ".foo23" cannot typecheck.
Method ".foo23" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
-       .bar:A
-       .foo123:A

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo23
""", List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo23;}
"""));}

@Test void tsOkIndirectFail3(){fail("""
001| A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
   |                            --------~~~~^^^^^^^^^

While inspecting ".bar" line 1
This call to method ".foo1123" cannot typecheck.
Method ".foo1123" is not declared on type "A".
Did you mean ".foo123" ?

Available methods on type "A":
-       .bar:A
-       .foo123:A

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo1123
""", List.of("""
A:{.foo123:A->this.foo123; .bar:A->this.foo1123;}
"""));}

@Test void tsOkIndirectFail4(){fail("""
003|   .bar:A->this.foo123(this);
   |   --------~~~~^^^^^^^^~~~~~

While inspecting ".bar" line 3
This call to method ".foo123(_)" cannot typecheck.
There are methods ".foo123" and ".foo123(_,_,_)" on type "A",
but with a different number of arguments.
This call supplies 1, but available methods take 0 or 3.

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123(this)
""", List.of("""
A:{
  .foo123:A->this.foo123;
  .bar:A->this.foo123(this);
  .foo123(A,A,A):A->this.foo123;
  }
"""));}

@Test void tsOkIndirectFail4spaces(){fail("""
003|   .bar:A->this.foo123(this      );
   |   --------~~~~^^^^^^^^~~~~-------

While inspecting ".bar" line 3
This call to method ".foo123(_)" cannot typecheck.
There are methods ".foo123" and ".foo123(_,_,_)" on type "A",
but with a different number of arguments.
This call supplies 1, but available methods take 0 or 3.

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123(this)
""", List.of("""
A:{
  .foo123:A->this.foo123;
  .bar:A->this.foo123(this      );
  .foo123(A,A,A):A->this.foo123;
  }
"""));}
@Test void tsOkIndirectFail5(){fail("""
001| A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
   |                            ------------~~~~^^^^^^^^

While inspecting ".bar" line 1
This call to method "A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "mut".
This call requires a receiver with capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123
""", List.of("""
A:{.foo123:A->this.foo123; mut .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail6a(){fail("""
001| A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
   |                            -------------~~~~^^^^^^^^

While inspecting ".bar" line 1
This call to method "A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123
""", List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123;}
"""));}//With inference we infer [imm] (next case)
@Test void tsOkIndirectFail6b(){fail("""
001| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                            -------------~~~~^^^^^^^^~~~~~

While inspecting ".bar" line 1
This call to method "A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123
""", List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}
@Test void tsOkIndirectFail6c(){fail("""
001| A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
   |                            -------------~~~~^^^^^^^^~~~~~~

While inspecting ".bar" line 1
This call to method ".foo123" cannot typecheck.
".foo123" exists on type "A", but not with the requested capability.
This call requires the existence of a "read" method.
Available capabilities for this method: "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123[read]
""", List.of("""
A:{.foo123:A->this.foo123; read .bar:A->this.foo123[read];}
"""));}
@Test void implicitRcIsInferredInNestedLiteral(){ok(List.of("""
Counter:{ mut .inc: mut Counter; mut .inc2: mut Counter }
Make:{ #: mut Counter -> mut Counter{'self
  mut .inc: mut Counter -> self;
  mut .inc2: mut Counter -> self.inc.inc;
  } }
"""));}

@Test void tsOkIndirectFail7(){fail("""
001| A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
   |                                ------------~~~~^^^^^^^^

While inspecting ".bar" line 1
This call to method "mut A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "imm".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123[mut]
""", List.of("""
A:{mut .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail8(){fail("""
001| A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
   |                                                            -------------~~~~^^^^^^^^~~~~~

While inspecting ".bar" line 1
This call to method "A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "imm".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123
""", List.of("""
A:{mut .foo123:A->this.foo123; imm .foo123:A->this.foo123; read .bar:A->this.foo123[imm];}
"""));}

@Test void tsOkIndirectInferredAsRead(){ok(List.of("""
A:{mut .foo123:A->this.foo123; read .foo123:A->this.foo123; imm .bar:A->this.foo123;}
"""));}
@Test void tsOkIndirectFail10(){fail("""
006|   read .bar:A->
007|     this.foo123[mut];
   |     ----^^^^^^^^-----

While inspecting ".bar" line 6
This call to method "mut A.foo123" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Compressed relevant code with inferred types: (compression indicated by `-`)
this.foo123[mut]
""", List.of("""
A:{
  mut .foo123:A->
    this.foo123;
  imm .foo123:A->
    this.foo123;
  read .bar:A->
    this.foo123[mut];
  }
"""));}
@Test void baseTypeError(){fail("""
001| A:{ .bar(b:B):A->b; }
   |     -------------^^

While inspecting parameter "b" > ".bar(_)" line 1
The body of method ".bar(_)" of type declaration "A" is an expression returning "B".
Parameter "b" has type "B" instead of a subtype of "A".

See inferred typing context below for how type "A" was introduced: (compression indicated by `-`)
A:{.bar(b:B):A->b}
""", List.of("""
A:{ .bar(b:B):A->b; }
B:{ }
"""));}
@Test void uncallableMethodOk(){ok(List.of("""
B:{ mut .bar:B }
A:{ mut .baz(b: B):B->{}; }
"""));}
@Test void uncallableMethodFail(){fail("""
002| A:{ mut .baz(b: mut B):read B-> { .bar->b}; }
   |     ----------------------------~~^^^^^^^~

While inspecting object literal instance of "read B" > ".baz(_)" line 2
The method "mut B.bar" is dead code.
The object literal instance of "B" is "read", so it will never be seen as "mut".
But it implements method "mut .bar", which requires a "mut" receiver.

Compressed relevant code with inferred types: (compression indicated by `-`)
read B{mut .bar:mut B->b}
""", List.of("""
B:{ mut .bar:mut B }
A:{ mut .baz(b: mut B):read B-> { .bar->b}; }
"""));}
@Test void immLiteralTwoSupersLeaveSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:{ mut .m: A }
User:{ #: A -> C:A,B{} }
"""));}
@Test void readLiteralTwoSupersLeaveSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:{ mut .m: A }
User:{ #: read A -> read C:A,B{} }
"""));}
@Test void readLiteralDiamondLeavesSameMutAbstract(){ok(List.of("""
A:{ mut .m: A }
B:A{}
D:A{}
User:{ #: read A -> read C:B,D{} }
"""));}
@Test void readLiteralImplementsReadOverloadOfMergedMutAbstract(){ok(List.of("""
Z:{}
A:{ mut .m: Z; read .m: Z }
B:{ mut .m: Z; read .m: Z }
User:{ #: read A -> read C:A,B{ .m -> Z } }
"""));}
@Test void methodReceiverNotRcc(){fail("""
003|   .bar[X:imm,mut,read](x:X):A->x.foo123;
   |   -----------------------------~^^^^^^^^

While inspecting ".bar(_)" line 3
This call to method ".foo123" cannot typecheck.
The receiver is of type "X". This is a generic type parameter.
Generic type parameters cannot be receivers of method calls.

See inferred typing context below for how type "X" was introduced: (compression indicated by `-`)
A:{.foo123:A->this.foo123;.bar[X:*](x:X):A->x.foo123}
""", List.of("""
A:{
  .foo123:A->this.foo123;
  .bar[X:imm,mut,read](x:X):A->x.foo123;
}
"""));}

@Test void methodTArgsArityError(){fail("""
003|   .bar:A->this.id[A,A](this);
   |   --------~~~~^^^^~~~~~~~~~~

While inspecting ".bar" line 3
This call to method "A.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
This method expects 1 generic type argument: "X"; but this call provides 2 generic type arguments.

Compressed relevant code with inferred types: (compression indicated by `-`)
this.id[imm,A,A](this)
""", List.of("""
A:{
  .id[X:imm,mut,read](x:X):X->x;
  .bar:A->this.id[A,A](this);
}
"""));}

@Test void methodArgsDisagree(){fail("""
003|   .caller(x:readH A, y:mutH A):A->this.f(x,y);
   |   --------------------------------~~~~^^^~~~~

While inspecting ".caller(_,_)" line 3
This call to method ".f(_,_)" cannot typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Parameter "x" has type "readH A" instead of a subtype of "read A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow mutH receiver, Allow mutH argument 2
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 fails:    Allow readH arguments, Allow mutH argument 1
  Parameter "y" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(x,y)
""", List.of("""
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,y);
}
"""));}

@Test void methodArgsDisagree2(){fail("""
004|   .caller(x:readH A, y:mutH A):A->this.f(x,ID#[mutH A]y);
   |   --------------------------------~~~~^^^~~~~~~~~~~~~~~~

While inspecting ".caller(_,_)" line 4
This call to method ".f(_,_)" cannot typecheck.
Each argument is compatible with at least one promotion, but no single promotion fits all arguments.

Compatible promotions by argument:
- Argument 1 has type "readH A" and is compatible with: Allow readH arguments, Allow mutH argument 1.
- Argument 2 has type "mutH A" and is compatible with: Allow mutH argument 2.

Promotion failures:
- Argument 1 fails:    As declared
  Parameter "x" has type "readH A" instead of a subtype of "read A".
- Argument 1 fails:    Strengthen result, Strengthen hygienic result, Allow mutH receiver, Allow mutH argument 2
  Parameter "x" has type "readH A" instead of a subtype of "imm A".
- Argument 2 fails:    Allow readH arguments, Allow mutH argument 1
  Method call "ID#(_)" has type "mutH A" instead of a subtype of "iso A".

Compressed relevant code with inferred types: (compression indicated by `-`)
this.f(x,ID#[imm,mutH A](y))
""", List.of("""
ID:{#[T:**](x:T):T->x}
A:{
  .f(a:read A, b:mut A):A->this;
  .caller(x:readH A, y:mutH A):A->this.f(x,ID#[mutH A]y);
}
"""));}

@Test void noVar1Ok(){ok(List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->Skip#(aaaa);
}
"""));}
@Test void noVar1Fail(){fail("""
004|   .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
   |   ---------------------------~~~~~~~~~~~~~~^^^^^--

While inspecting parameter "aaaa" > ".foo" line 4 > ".f(_)" line 4
Parameter "aaaa" has type "mut A".
Parameter "aaaa" can observe mutation; thus it cannot be captured in the "imm" object literal "BB" (line 4).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
aaaa
""", List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm BB:B{.foo:B->Skip#(aaaa);}
}
"""));}

@Test void noVar1FailAnon(){fail("""
004|   .f(aaaa:mut A):B->imm B{.foo:B->Skip#(aaaa);}
   |   ------------------------~~~~~~~~~~~~~~^^^^^--

While inspecting parameter "aaaa" > ".foo" line 4 > ".f(_)" line 4
Parameter "aaaa" has type "mut A".
Parameter "aaaa" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "B" (line 4).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
aaaa
""", List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):B->imm B{.foo:B->Skip#(aaaa);}
}
"""));}

@Test void noVarPassesWithRCFilters(){ok(List.of("""
Skip:{#[X:**](X):B->B}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(aaaa);}
}
"""));}

@Test void fullyAnnotetedDeepCall(){ok(List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#[imm,read A](Id#[imm,read A](aaaa));}}
"""));}
@Test void deepCall(){ok(List.of("""
Skip:{#[X:**](X):B->B}
Id:{#[X:**](x:X):X->x}
B:{}
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Skip#(Id#(aaaa));}}
"""));}

@Test void hopelessArg_calls_pArgHasType(){fail("""
006|   .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
   |                                    -------------~~~~^^~~~~~~~~~~~~~-

While inspecting ".foo" line 6 > ".f(_)" line 6
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mut A" or "iso A".
Method call "AsRead#(_)" has type "read A" instead of a subtype of "mut A".

Type required by each promotion:
- "mut A"  (As declared)
- "iso A"  (Strengthen result)

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
A:{.f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa))}}
""", List.of("""

B:{}
Need:{ #(a:mut A):B->B{} }
AsRead:{ #(x:read A):read A->x }
A:{
  .f(aaaa:mut A):read B->read BB:B{read .foo:B->Need#(AsRead#(aaaa));}
}
"""));}

@Test void bestLitName_anonLiteralNoImpl_withMeth(){ok(List.of("""
A:{}
Main:{
  .m:A -> {.foo:A->A }.foo
}
"""));}


@Test void err_bestLitName_anonLiteralNoImpl_missingMethod(){fail("""
003|   .m:A -> { .bar:A->A }.foo
   |   --------~~~~~~~~~~~~~^^^^

While inspecting ".m" line 3
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on object literal instance of "A".

Available methods on object literal instance of "A":
-       .bar:A

Compressed relevant code with inferred types: (compression indicated by `-`)
A{.bar:A->A}.foo
""", List.of("""
A:{}
Main:{
  .m:A -> { .bar:A->A }.foo
  }
"""));}

@Test void err_bestLitName_anonLiteralNoImpl_empty(){fail("""
004|    .m:A -> { }.foo
   |    --------~~~^^^^

While inspecting ".m" line 4
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on type "A".
Type "A" does not have any methods.

Compressed relevant code with inferred types: (compression indicated by `-`)
A.foo
""", List.of("""

A:{}
 Main:{
   .m:A -> { }.foo
  }
"""));}
@Test void err_bestLitName_NamedLiteralNoImpl_empty(){fail("""
003|    .m:A -> B:{ }.foo
   |    --------~~~~~^^^^

While inspecting ".m" line 3
This call to method ".foo" cannot typecheck.
Method ".foo" is not declared on object literal instance of "B".
Type "B" does not have any methods.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:{}.foo
""", List.of("""
A:{}
 Main:{
   .m:A -> B:{ }.foo
  }
"""));}
@Test void anonReceiverSealedHeadSelfCall(){ok(List.of("""
Outer:{ .m: base.Void -> {'self .a: base.Void -> base.Void{}; .b: base.Void -> self.a }.b }
"""));}
@Test void anonReceiverSealedHead(){ok(List.of("""
Outer:{ .m: base.Void -> { .a: base.Void -> base.Void{} }.a }
"""));}
@Test void err_anonReceiverSealedHeadReturnsSelf(){fail("""
001| Outer:{ .m: base.Void -> {'self .a: Outer -> self}.a }
   |         ------------------------~~~~~~~~~~~~~^^^^^--

While inspecting parameter "self" > ".a" line 1 > ".m" line 1
Method ".a" inside the object literal "{...}" (line 1)
is implemented with an expression returning the anonymous type of the object literal at line 1, column 26.
Parameter "self" has type the anonymous type of the object literal at line 1, column 26 instead of a subtype of "Outer".

See inferred typing context below for how type "Outer" was introduced: (compression indicated by `-`)
Outer:{.m:-.Void->{'self .a:Outer->self}.a}
""", List.of("""
Outer:{ .m: base.Void -> {'self .a: Outer -> self}.a }
"""));}
@Test void err_anonReceiverSealedHeadUnwrittenSig(){failWf("""
001| Outer:{ .m: base.Void -> { .a -> base.Void{} }.a }
   |                          --^^^^^^^^^^^^^^^^^--

While inspecting object literal instance of "_AOute"
Missing return type for method ".a".
Add an explicit return type before '->'.
Alternatively (less common), if you intended to override and omit the signature,
the signature must be inherited from a supertype.
Cannot infer signature of method ".a".
No supertype has a method named ".a" with 0 parameters.
""", List.of("""
Outer:{ .m: base.Void -> { .a -> base.Void{} }.a }
"""));}
@Test void anonReceiverSealedHeadCapturesGeneric(){ok(List.of("""
Outer:{ .m[X](x:X): base.Void -> { .a: X -> x; .b[Y](y:Y): Y -> y }.b(base.Void) }
"""));}
@Test void anonReceiverImplementableHeadGivesSignatures(){ok(List.of("""
A:{ .get(x:A): A }
Main:{ .m(a:A): A -> { .get(x) -> x }.get(a) }
"""));}
@Test void anonReceiverSealedHeadSamePkgGivesSignatures(){ok(List.of("""
S:base.Sealed{ .get(x:S): S }
Main:{ .m(s:S): S -> { .get(x) -> x }.get(s) }
"""));}

@Test void passInt(){ok(List.of("""
 Main:{ .m:base.Int -> +42 }
"""));}
@Test void passFloat(){ok(List.of("""
 Main:{ .m:base.Float -> +42.0 }
"""));}
@Test void passNat(){ok(List.of("""
 Main:{ .m:base.Nat -> 42 }
"""));}
@Test void passSStr(){ok(List.of("""
 Main:{ .m:base.Str -> `Hi` }
"""));}
@Test void passDStr(){ok(List.of("""
 Main:{ .m:base.Str -> "Hi" }
"""));}
@Test void failFloatForInt_compressedKeepsFloat(){fail("""
001|  Main:{ .m:base.Int -> +1.5 }
   |         ---------------^^^^

While inspecting object literal instance of "base.Float" > ".m" line 1
The body of method ".m" of type declaration "Main" is an expression returning "iso base.Float".
Object literal is of type "base.Float" instead of a subtype of "base.Int".

See inferred typing context below for how type "base.Int" was introduced: (compression indicated by `-`)
Main:{.m:-.Int->+1.5}
""", List.of("""
 Main:{ .m:base.Int -> +1.5 }
"""));}
@Test void failIntTooBig(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Int -> +421381834238972893748972389723 }
   |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Integer literal is out of range for "base.Int".
"base.Int" must be representable as a 64-bit signed integer.
Valid range: -9223372036854775808 .. 9223372036854775807.
This literal is: "421381834238972893748972389723".
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Int -> +421381834238972893748972389723 }
"""));}
@Test void failNatTooBig(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Nat -> 421381834238972893748972389723 }
   |                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting the file
Natural literal is out of range for "base.Nat".
"base.Nat" must be representable as a 64-bit unsigned integer.
Valid range: 0 .. 18446744073709551615.
This literal is: "421381834238972893748972389723".
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Nat -> 421381834238972893748972389723 }
"""));}

@Test void failFloatTooBig(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e309 }
   |                          ^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e309".
This literal overflows; the nearest representable value is "+179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e309 }
"""));}
@Test void failFloatExponentBeyondIntRange(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e99999999999 }
   |                          ^^^^^^^^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e99999999999".
This literal overflows; the nearest representable value is "+179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e99999999999 }
"""));}
@Test void failFloatNegativeExponentBeyondIntRange(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e-99999999999 }
   |                          ^^^^^^^^^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e-99999999999".
If rounded, the nearest representable value is "+0.0".
Write "+1.0e-99999999999soft" to accept that rounding.
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e-99999999999 }
"""));}
@Test void okFloatZeroExponentBeyondIntRange(){ok(List.of("""
 Main:{ .m:base.Float -> +0.0e-99999999999 }
"""));}
@Test void failNumberLiteralWithTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: A -> 1[A] }
   |              ^^

While inspecting a literal
Literal "1" is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after "1".
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: A -> 1[A] }
"""));}
@Test void failNumberLiteralWithEmptyTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: A -> 1[] }
   |              ^^

While inspecting a literal
Literal "1" is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after "1".
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: A -> 1[] }
"""));}
@Test void failStrLiteralWithTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: `a`[A] }
   |         ^^^^

While inspecting a literal
Literal "`a`" is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after "`a`".
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: `a`[A] }
"""));}
@Test void failUStrLiteralWithTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: "a"[A] }
   |         ^^^^

While inspecting a literal
Literal `"a"` is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after `"a"`.
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: "a"[A] }
"""));}
@Test void failFloatLiteralWithTypeParameters(){failExt("""
In file: [###].fear

001| A:{ .m: A -> -1.5[] }
   |              ^^^^^

While inspecting a literal
Literal "-1.5" is directly followed by "[".
Number and string literals take no generic type arguments.
Remove the "[...]" after "-1.5".
Error 2 UnexpectedToken
""", List.of("""
A:{ .m: A -> -1.5[] }
"""));}
@Test void failFloatTooSmall(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e-400 }
   |                          ^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e-400".
If rounded, the nearest representable value is "+0.0".
Write "+1.0e-400soft" to accept that rounding.
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e-400 }
"""));}
@Test void failFloatImprecise1(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +0.1 }
   |                          ^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+0.1".
If rounded, the nearest representable value is "+0.1000000000000000055511151231257827021181583404541015625".
Write "+0.1soft" to accept that rounding.
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +0.1 }
"""));}
@Test void failFloatImprecise2(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +0.2 }
   |                          ^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+0.2".
If rounded, the nearest representable value is "+0.200000000000000011102230246251565404236316680908203125".
Write "+0.2soft" to accept that rounding.
Hint: if you need arbitrary precision numbers, use "base.Num".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +0.2 }
"""));}
@Test void everyZeroLiteralIsThePositiveZero(){
  assertEquals(List.of("0.0d", "0.0d", "0.0d", "0.0d", "0.0d"),
    List.of("-0.0", "+0.0", "0.0", "-0__0.000", "-0.0e5").stream().map(LiteralDeclarations::toJavaLiteral).toList());
}
@Test void floatExactFearlessLitScientific(){
  assertEquals("+9.31322574615478515625e-10", LiteralDeclarations.floatExactFearlessLit(Math.scalb(1.0, -30)));
  assertEquals("-9.31322574615478515625e-10", LiteralDeclarations.floatExactFearlessLit(-Math.scalb(1.0, -30)));
}
@Test void okFloatTooBig(){ok(List.of("""
 Main:{ .m:base.Float -> +179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0 }
"""));}
@Test void okFloatPrecise1(){ok(List.of("""
 Main:{ .m:base.Float ->  +0.1000000000000000055511151231257827021181583404541015625 }
"""));}
@Test void okFloatPrecise2(){ok(List.of("""
 Main:{ .m:base.Float -> +0.200000000000000011102230246251565404236316680908203125 }
"""));}
@Test void okFloatSoft(){ok(List.of("""
 Main:{ .m:base.Float -> +0.1soft }
"""));}
@Test void okFloatSoftUnsigned(){ok(List.of("""
 Main:{ .m:base.Float -> 0.4soft }
"""));}
@Test void okFloatSoftAlreadyExact(){ok(List.of("""
 Main:{ .m:base.Float -> +0.5soft }
"""));}
@Test void okFloatSoftUnderscores(){ok(List.of("""
 Main:{ .m:base.Float -> +1_0.4soft }
"""));}
@Test void failFloatSoftTooBig(){failExt("""
In file: [###].fear

001|  Main:{ .m:base.Float -> +1.0e309soft }
   |                          ^^^^^^^^^^^^

While inspecting the file
Float literal is not exactly representable as "base.Float".
"base.Float" must be representable exactly as a 64-bit IEEE 754 double.
This literal is: "+1.0e309soft".
This literal overflows; the nearest representable value is "+179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0".
Error 7 WellFormedness
""", List.of("""
 Main:{ .m:base.Float -> +1.0e309soft }
"""));}

@Test void byNameOk1(){ok(List.of("""
 A:{.foo:A->A}
 B:A{}
 Main:{ .m:B -> B }
"""));}
@Test void byNameOk2(){ok(List.of("""
 A:{.foo:A->A}
 B:A{}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}
@Test void byNameFail1(){fail("""
003|  Main:{ .m:B -> B }
   |         --------^

While inspecting object literal instance of "iso B" > ".m" line 3
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "A".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso B
""", List.of("""
 A:{.foo:A}
 B:A{}
 Main:{ .m:B -> B }
"""));}
@Test void byNameFail2(){fail("""
003|  Main:{ .m:B -> B{.bar:A->A} }
   |         --------^^----------

While inspecting object literal instance of "iso B" > ".m" line 3
This object literal is missing a required method.
Missing: "imm .foo".
Required by: "B".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso B{.bar:A->A}
""", List.of("""
 A:{.foo:A->A}
 B:A{.foo:A}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}

@Test void byNameOkMut(){ok(List.of("""
 A:{mut .foo:A->A}
 B:A{.foo:A}
 Main:{ .m:B -> B{.bar:A->A} }
"""));}

@Test void captureFreeThisIsNotMut(){fail("""
002|  B:A,base.CaptureFree{ .get->this; }
   |                        ------^^^^^

While inspecting parameter "this" > ".get" line 2
The body of method ".get" of type declaration "B" is an expression returning "B".
Parameter "this" has type "B" instead of a subtype of "mut A".
Hint: type declaration "B" implements "base.CaptureFree", so parameter "this" is "imm" in every method.
A value of "B" is never "mut", so "mut .get" can stay abstract.
A method written without a receiver capability also implements "mut .get": write the receiver capability, as in "read .get".

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
B:A,-.Cap-ree{read .get:read A->this;mut .get:mut A->this}
""", List.of("""
 A:{ read .get: read A; mut .get: mut A; }
 B:A,base.CaptureFree{ .get->this; }
"""));}
@Test void captureFreeThisReadOnly(){ok(List.of("""
 A:{ read .get: read A; mut .get: mut A; }
 B:A,base.CaptureFree{ read .get->this; }
 Main:{ .m:B -> B }
"""));}
@Test void byNameAbstractMutImm(){ok(List.of("""
 A:{mut .foo:A}
 B:A{}
 Main:{ .m:B -> B }
"""));}
@Test void byNameAbstractMutMut(){fail("""
003|  Main:{ .m:mut B -> mut B }
   |         ----------------^

While inspecting object literal instance of "iso B" > ".m" line 3
This object literal is missing a required method.
Missing: "mut .foo".
Required by: "A".
Hint: add an implementation for ".foo" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso B
""", List.of("""
 A:{mut .foo:A}
 B:A{}
 Main:{ .m:mut B -> mut B }
"""));}

@Test void simpleBox(){ok(List.of("""
Box[EE:*]:{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  }
Boxs1:{#[ET:*](e:ET):mut Box[ET]->{
  mut .get ->e;
  read .get ->e;
  imm .get ->e;
  }}
Boxs:{#[ET:*](e:ET):mut Box[ET]->{e}}
"""));}

@Test void toStr(){ok(List.of("""
Str:{}
ToStr:{ read .str: Str }
ToStrBy[T]:{#(read T):read ToStr}
ToStr[E:*]:{ read .str(ToStrBy[imm E]): Str }
Box[EE:*]: ToStr[EE]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .str by-> by#(this.get).str
  }
A:ToStr{ .str->Str}
Top:{
  .m00(b:Box[A]):Str -> b.str {::};
  .m01(b:Box[read A]):Str -> b.str {::};
  .m02(b:Box[mut A]):Str -> b.str {::};
  .m03(b:read Box[A]):Str -> b.str {::};
  .m04(b:read Box[read A]):Str -> b.str {::};
  .m05(b:read Box[mut A]):Str -> b.str {::};
  .m06(b:mut Box[A]):Str -> b.str {::};
  .m07(b:mut Box[read A]):Str -> b.str {::};
  .m08(b:mut Box[mut A]):Str -> b.str {::};
  .m09(b:iso Box[A]):Str -> b.str {::};
  .m10(b:iso Box[read A]):Str -> b.str {::};
  .m11(b:iso Box[mut A]):Str -> b.str {::};
  .m12(b:readH Box[A]):Str -> b.str {::};
  .m13(b:readH Box[read A]):Str -> b.str {::};
  .m14(b:readH Box[mut A]):Str -> b.str {::};
  .m15(b:mutH Box[A]):Str -> b.str {::};
  .m16(b:mutH Box[read A]):Str -> b.str {::};
  .m17(b:mutH Box[mut A]):Str -> b.str {::};
  }
"""));}
@Test void toStrToImm(){ok(List.of("""
Str:{}
ToStr:{ read .str: Str }
ToStrBy[T]:{#(read T):read ToStr}
ToStr[E:*]:{ read .str(ToStrBy[imm E]): Str }
ToImm[T]:{ read .imm: T }
ToImmBy[T]:{#(read T):read ToImm[T]}
ToImm[T,E:*,TE]:{ read .imm(ToImmBy[imm E]): TE }
Box[EE:*]: ToStr[EE], ToImm[Box[EE],EE,Box[imm EE]]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .str by-> by#(this.get).str;
  .imm by-> Boxs#(by#(this.get).imm);
  }
Boxs1:{#[ET:*](e:ET):mut Box[ET]->{
  mut .get ->e;
  read .get ->e;
  imm .get ->e;
  }}
Boxs:{#[ET:*](e:ET):mut Box[ET]->{e}}

A:ToStr,ToImm[A]{ .str->Str; .imm->A}
TopToStr:{
  .m00(b:Box[A]):Str -> b.str {::};
  .m01(b:Box[read A]):Str -> b.str {::};
  .m02(b:Box[mut A]):Str -> b.str {::};
  .m03(b:read Box[A]):Str -> b.str {::};
  .m04(b:read Box[read A]):Str -> b.str {::};
  .m05(b:read Box[mut A]):Str -> b.str {::};
  .m06(b:mut Box[A]):Str -> b.str {::};
  .m07(b:mut Box[read A]):Str -> b.str {::};
  .m08(b:mut Box[mut A]):Str -> b.str {::};
  .m09(b:iso Box[A]):Str -> b.str {::};
  .m10(b:iso Box[read A]):Str -> b.str {::};
  .m11(b:iso Box[mut A]):Str -> b.str {::};
  .m12(b:readH Box[A]):Str -> b.str {::};
  .m13(b:readH Box[read A]):Str -> b.str {::};
  .m14(b:readH Box[mut A]):Str -> b.str {::};
  .m15(b:mutH Box[A]):Str -> b.str {::};
  .m16(b:mutH Box[read A]):Str -> b.str {::};
  .m17(b:mutH Box[mut A]):Str -> b.str {::};
  }
TopToImm:{
  .m00(b:Box[A]):Box[A] -> b.imm {::};
  .m01(b:Box[read A]):Box[A] -> b.imm {::};
  .m02(b:Box[mut A]):Box[A] -> b.imm {::};
  .m03(b:read Box[A]):Box[A] -> b.imm {::};
  .m04(b:read Box[read A]):Box[A] -> b.imm {::};
  .m05(b:read Box[mut A]):Box[A] -> b.imm {::};
  .m06(b:mut Box[A]):Box[A] -> b.imm {::};
  .m07(b:mut Box[read A]):Box[A] -> b.imm {::};
  .m08(b:mut Box[mut A]):Box[A] -> b.imm {::};
  .m09(b:iso Box[A]):Box[A] -> b.imm {::};
  .m10(b:iso Box[read A]):Box[A] -> b.imm {::};
  .m11(b:iso Box[mut A]):Box[A] -> b.imm {::};
  .m12(b:readH Box[A]):Box[A] -> b.imm {::};
  .m13(b:readH Box[read A]):Box[A] -> b.imm {::};
  .m14(b:readH Box[mut A]):Box[A] -> b.imm {::};
  .m15(b:mutH Box[A]):Box[A] -> b.imm {::};
  .m16(b:mutH Box[read A]):Box[A] -> b.imm {::};
  .m17(b:mutH Box[mut A]):Box[A] -> b.imm {::};
  }
"""));}
@Test void toOrder(){ok(List.of("""
use base.Bool as Bool; use base.True as True; use base.False as False; use base.Block as Block; use base.F as F;
Str:{}
OrderMatch[R:**]:{ mut .lt:R; mut .eq:R; mut .gt:R; }
Order[T]: {
  read .close:read T;
  read .cmp[R:**](a:read T,b:read T,m: mut OrderMatch[R]): R;
  read ==  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> False});
  read <=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->True; .gt -> False});
  read >=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> True});
  read <   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> False});
  read >   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->False; .gt -> True});
  read !=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> True});
  }
OrderBy[T]:{
  #(read T):read Order[T];
  .then(other:OrderBy[T]):OrderByCmp[T] -> {
    .cmp(a,b,m)-> this#a
      .cmp(a,b,{.lt ->m.lt; .eq ->other#a.cmp(a,b,m); .gt ->m.gt})
    };
  .view[AA](f:F[read AA,read Order[T]]):OrderByCmp[AA] -> {a,b,m-> f#a.cmp(f#a.close,f#b.close,m)};
}
OrderByCmp[T]:OrderBy[T]{
  .cmp[R:**](a:read T,b:read T,m:mut OrderMatch[R]): R;
  # a0 -> { .close -> a0; .cmp a,b,m -> this.cmp(a,b,m) };
  }
Order[T,E:*]:{
  read .close:read T;
  read .cmp[R:**](by: OrderBy[imm E], a:read T,b:read T, m: mut OrderMatch[R]): R;
  read .order(by: OrderBy[imm E]): read Order[T] -> {
    .close -> this.close;
    .cmp a,b,m -> this.cmp(by,a,b,m);
    };
  }
Box[EE:*]: Order[Box[EE],EE]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .close->this;
  .cmp by, a, b, m-> by#(a.get).cmp(a.get[read],b.get[read],m);
  }
A:Order[A]{ .close->this; .cmp a, b, m-> m.eq}
Top:{
  .m00(b:Box[A]):Bool -> b.order{::} == b;
  .m01(b:Box[read A]):Bool -> b.order{::} == b;
  .m02(b:Box[mut A]):Bool -> b.order{::} == b;
  .m03(b:read Box[A]):Bool -> b.order{::} == b;
  .m04(b:read Box[read A]):Bool -> b.order{::} == b;
  .m05(b:read Box[mut A]):Bool -> b.order{::} == b;
  .m06(b:mut Box[A]):Bool -> b.order{::} == b;
  .m07(b:mut Box[read A]):Bool -> b.order{::} == b;
  .m08(b:mut Box[mut A]):Bool -> b.order{::} == b;
  .m09(b1:iso Box[A],b2:iso Box[A]):Bool -> b1.order{::} == b2;
  .m10(b1:iso Box[read A],b2:iso Box[read A]):Bool -> b1.order{::} == b2;
  .m11(b1:iso Box[mut A],b2:iso Box[mut A]):Bool -> b1.order{::} == b2;
  .m12(b:readH Box[A]):Bool -> b.order{::} == b;
  .m13(b:readH Box[read A]):Bool -> b.order{::} == b;
  .m14(b:readH Box[mut A]):Bool -> b.order{::} == b;
  .m15(b:mutH Box[A]):Bool -> b.order{::} == b;
  .m16(b:mutH Box[read A]):Bool -> b.order{::} == b;
  .m17(b:mutH Box[mut A]):Bool -> b.order{::} == b;
  }
"""));}
static String flatMapDecs= """
use base.F as F;
List[E:*]:{}
Cat:{}
Person:{ .cats: List[Cat]; .mcats: mut List[Cat]; }
Flow[E:*]:{ mut .flatMap[R:*](f: read F[E, read List[R]]): mut Flow[read/imm R] }
""";
@Test void lambdaKeepsTheReadTypeArgumentOfItsParameter(){ok(List.of(flatMapDecs+"""
User:{ .m(ps: mut Flow[Person]): mut Flow[Cat] -> ps.flatMap{::.cats} }
"""));}
@Test void lambdaKeepsTheReadTypeArgumentOfItsParameterWithTargs(){ok(List.of(flatMapDecs+"""
User:{ .m(ps: mut Flow[Person]): mut Flow[Cat] -> ps.flatMap[Cat]{::.cats} }
"""));}
@Test void lambdaKeepsTheReadTypeArgumentOfItsParameterMutBody(){ok(List.of(flatMapDecs+"""
User:{ .m(ps: mut Flow[Person]): mut Flow[Cat] -> ps.flatMap{::.mcats} }
"""));}
@Test void lambdaKeepsTheReadTypeArgumentOfItsParameterExplicitHead(){ok(List.of(flatMapDecs+"""
User:{ .m(ps: mut Flow[Person]): mut Flow[Cat] -> ps.flatMap(read F[Person, read List[Cat]]{::.mcats}) }
"""));}
@Test void lambdaKeepsTheReadTypeVariableArgumentOfItsParameter(){ok(List.of(flatMapDecs+"""
Viewer[T]:{ .view[A](f: F[read A, read T]): Viewer[A] }
User:{ .m[T](v: Viewer[T], x: imm T): Viewer[Cat] -> v.view{c -> x} }
"""));}
@Test void lambdaKeepsTheReadTypeVariableArgumentOfItsParameterMutBody(){ok(List.of(flatMapDecs+"""
Viewer[T:*]:{ .view[A](f: F[read A, read T]): Viewer[A] }
User:{ .m[T:*](v: Viewer[T], x: F[mut T]): Viewer[Cat] -> v.view{c -> x#} }
"""));}
@Test void toOrderHash(){ok(List.of("""
use base.Nat as Nat; use base.Bool as Bool; use base.True as True; use base.False as False; use base.Block as Block; use base.F as F;
Str:{}
OrderMatch[R:**]:{ mut .lt:R; mut .eq:R; mut .gt:R; }
Order[T]: {
  read .close:read T;
  read .cmp[R:**](a:read T,b:read T,m: mut OrderMatch[R]): R;
  read ==  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> False});
  read <=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->True; .gt -> False});
  read >=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> True});
  read <   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> False});
  read >   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->False; .gt -> True});
  read !=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> True});
  }
OrderBy[T]:{
  #(read T):read Order[T];
  .then(other:OrderBy[T]):OrderByCmp[T] -> {
    .cmp a,b,m -> this#a
      .cmp(a,b,{.lt ->m.lt; .eq ->other#a.cmp(a,b,m); .gt ->m.gt})
    };
  .thenKey[TF](k:FF[T,TF]): OrderByCmp[T] -> this.then(By2#k);
  .view[A](f:F[read A,read T]):OrderByCmp[A] -> {a,b,m -> this#(f#a).cmp(f#a,f#b,m)};
}
OrderByCmp[T]:OrderBy[T]{
  .cmp[R:**](a:read T,b:read T,m:mut OrderMatch[R]): R;
  # a0 -> { .close -> a0; .cmp a,b,m -> this.cmp(a,b,m) };
  }
Order[T,E:*]:{
  read .close:read T;
  read .cmp[R:**](by: OrderBy[imm E], a:read T,b:read T, m: mut OrderMatch[R]): R;
  read .order(by: OrderBy[imm E]): read Order[T] -> {
    .close -> this.close;
    .cmp a,b,m -> this.cmp(by,a,b,m);
    };
  }
Hasher: {
  mut #[A,B](a: read OrderHash[A], b: read OrderHash[B]): Nat -> a.hash(this) * 31 + (b.hash(this));
  }
OrderHash[T]:Order[T]{ read .hash(h: mut Hasher): Nat }
OrderHash[T,E:*]:Order[T,E]{
  read .hash(by: OrderHashBy[imm E], h: mut Hasher): Nat;
  read .orderHash(by: OrderHashBy[imm E]): read OrderHash[T] -> {
    .close -> this.close;
    .cmp a,b,m -> this.cmp(by,a,b,m);
    .hash h -> this.hash(by,h);
    };
  }
OrderHashBy[T]:OrderBy[T]{
  #(x:read T): read OrderHash[T];
  .thenHash(other: OrderHashBy[T]): OrderHashByCmp[T] -> {
    .cmp a,b,m -> this#a
      .cmp(a,b,{.lt ->m.lt; .eq ->other#a.cmp(a,b,m); .gt ->m.gt});
    .hash a,h -> h#(this#a, other#a);
    };
  .viewHash[A](f:F[read A,read T]):OrderHashByCmp[A] -> {
    .cmp a,b,m -> this#(f#a).cmp(f#a,f#b,m);
    .hash a,h -> this#(f#a).hash(h);
    };
  }
OrderHashByCmp[T]:OrderHashBy[T]{
  .cmp[R:**](a:read T,b:read T,m:mut OrderMatch[R]): R;
  .hash(a: read T,h: mut Hasher):Nat;
  # a0 -> {
    .close -> a0;
    .cmp a,b,m -> this.cmp(a,b,m);
    .hash h -> this.hash(a0,h);
    };
  }
Box[EE:*]: OrderHash[Box[EE],EE]{
  mut  .get: EE;
  read .get: read/imm EE;
  imm  .get: imm EE;
  .close->this;
  .cmp by, a, b, m-> by#(a.get).cmp(a.get[read],b.get[read],m);
  .hash by, h -> by#(this.get).hash h;
  }
A1:OrderHash[A1]{
  .close -> this;
  .cmp a, b, m -> m.eq;
  .hash h -> 0;
  }
Top:{
  .m00(b:Box[A1]):Bool -> b.order{::} == b;
  .m01(b:Box[read A1]):Bool -> b.order{::} == b;
  .m02(b:Box[mut A1]):Bool -> b.order{::} == b;
  .m03(b:read Box[A1]):Bool -> b.order{::} == b;
  .m04(b:read Box[read A1]):Bool -> b.order{::} == b;
  .m05(b:read Box[mut A1]):Bool -> b.order{::} == b;
  .m06(b:mut Box[A1]):Bool -> b.order{::} == b;
  .m07(b:mut Box[read A1]):Bool -> b.order{::} == b;
  .m08(b:mut Box[mut A1]):Bool -> b.order{::} == b;
  .m09(b1:iso Box[A1],b2:iso Box[A1]):Bool -> b1.order{::} == b2;
  .m10(b1:iso Box[read A1],b2:iso Box[read A1]):Bool -> b1.order{::} == b2;
  .m11(b1:iso Box[mut A1],b2:iso Box[mut A1]):Bool -> b1.order{::} == b2;
  .m12(b:readH Box[A1]):Bool -> b.order{::} == b;
  .m13(b:readH Box[read A1]):Bool -> b.order{::} == b;
  .m14(b:readH Box[mut A1]):Bool -> b.order{::} == b;
  .m15(b:mutH Box[A1]):Bool -> b.order{::} == b;
  .m16(b:mutH Box[read A1]):Bool -> b.order{::} == b;
  .m17(b:mutH Box[mut A1]):Bool -> b.order{::} == b;
  }
ThenHashBoxAll:{
  .thA_A(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  .thR_R(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  .thM_M(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  }
ThenHashLeBoxAll:{
  .leA_A(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1],y:read Box[A1]):Bool ->
    o.thenHash(p)#x <= y;
  .leR_R(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1],y:read Box[read A1]):Bool ->
    o.thenHash(p)#x <= y;
  .leM_M(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1],y:read Box[mut A1]):Bool ->
    o.thenHash(p)#x <= y;
  }
ThenLeSelf:{
  .leA(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1]):Bool -> o.then(p)#x <= x;
  .leR(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1]):Bool -> o.then(p)#x <= x;
  .leM(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1]):Bool -> o.then(p)#x <= x;
}
ViewBoxAll18:{
  .v00(by:OrderBy[A1],b:Box[A1],c:Box[A1]):Bool -> by.view({x->x.get})#b <= c;
  .v01(by:OrderBy[A1],b:read Box[A1],c:read Box[A1]):Bool -> by.view{x->x.get}#b <= c;
  .v02(by:OrderBy[A1],b:mut Box[A1],c:mut Box[A1]):Bool -> by.view{::.get}#b <= c;
  .v03(by:OrderBy[A1],b1:iso Box[A1],b2:iso Box[A1]):Bool -> by.view({x->x.get})#b1 == b2;
  .v04(by:OrderBy[A1],b:readH Box[A1],c:readH Box[A1]):Bool -> by.view({x->x.get})#b != c;
  .v05(by:OrderBy[A1],b:mutH Box[A1],c:mutH Box[A1]):Bool -> by.view({x->x.get})#b >= c;

  .v06(by:OrderBy[A1],b:Box[read A1],c:Box[read A1]):Bool -> by.view({x->x.get})#b > c;
  .v07(by:OrderBy[A1],b:read Box[read A1],c:read Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v08(by:OrderBy[A1],b:mut Box[read A1],c:mut Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v09(by:OrderBy[A1],b1:iso Box[read A1],b2:iso Box[read A1]):Bool -> by.view({x->x.get})#b1 <= b2;
  .v10(by:OrderBy[A1],b:readH Box[read A1],c:readH Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v11(by:OrderBy[A1],b:mutH Box[read A1],c:mutH Box[read A1]):Bool -> by.view({x->x.get})#b <= c;

  .v12(by:OrderBy[A1],b:Box[mut A1],c:Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v13(by:OrderBy[A1],b:read Box[mut A1],c:read Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v14(by:OrderBy[A1],b:mut Box[mut A1],c:mut Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v15(by:OrderBy[A1],b1:iso Box[mut A1],b2:iso Box[mut A1]):Bool -> by.view({x->x.get})#b1 <= b2;
  .v16(by:OrderBy[A1],b:readH Box[mut A1],c:readH Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v17(by:OrderBy[A1],b:mutH Box[mut A1],c:mutH Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;

  .vh0(by:OrderHashBy[A1],b:readH Box[mut A1],c:readH Box[mut A1]):Bool -> by.viewHash({x->x.get})#b <= c;
  .vh1(by:OrderHashBy[A1],b:mutH Box[mut A1],h:iso Hasher):Nat -> by.viewHash({x->x.get})#b .hash h;
  .vh2(by:OrderHashBy[A1],b:mut Box[mut A1],h:mut Hasher):Nat -> by.viewHash({x->x.get})#b .hash h;
}
By:{ #[T](by: OrderBy[T]): OrderBy[T] -> by; }
ByHash:{ #[T](by: OrderHashBy[T]): OrderHashBy[T] -> by; }

Age:OrderHash[Age]{ read .close->this; read .cmp a,b,m->m.eq; read .hash h->0; }
Name:OrderHash[Name]{ read .close->this; read .cmp a,b,m->m.eq; read .hash h->0; }
Person:{ read .age: Age; read .name: Name; }

AndThenTests:{
  read .orderOk0: OrderBy[Person] ->
    By#[Age]{::}.view[Person]{::.age};
  read .orderOk1: OrderBy[Person] ->
    By#[Age]{::}.view{::.age};
  read .orderOk: OrderBy[Person] ->
    By#[Age]{::}.view{::.age}
    .then(By#[Name]{::}.view({p->p.name}));
  read .hashOk: OrderHashBy[Person] ->
    ByHash#[Age]{::}.viewHash{::.age}
    .thenHash(ByHash#[Name]{::}.viewHash{::.name});
}
FF[A,T]:{#(read A): read Order[T]}
By2:{
  #[T,A](f:FF[A,T]): OrderByCmp[A] -> {
    .cmp a,b,m -> (f#a).cmp((f#a).close,(f#b).close,m);
  };
}
AndThenTests2:{
  read .orderOk0: OrderBy[Person] ->
    By2#{::.age};
  read .orderOk: OrderBy[Person] ->
    By2#{::.age}.thenKey{::.name};
  }
"""));}
@Test void toOrderHashDesign3(){ok(List.of("""
use base.Nat as Nat; use base.Bool as Bool; use base.True as True; use base.False as False; use base.Block as Block; use base.F as F;
Str:{}
ToStr:{ read .str: Str }
ToStrBy[T]:{#(read T):read ToStr}
ToStr[E:*]:{ read .str(ToStrBy[imm E]): Str }

OrderMatch[R:**]:{ mut .lt:R; mut .eq:R; mut .gt:R; }

Order[T]: {
  read .close: read T;
  read .cmp[R:**](t0: read T, t1: read T, m: mut OrderMatch[R]): R;

  read ==  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> False});
  read <=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->True; .gt -> False});
  read >=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->True; .gt -> True});
  read <   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> False});
  read >   (other: read T): Bool -> this.cmp(this.close, other,{.lt ->False;.eq ->False; .gt -> True});
  read !=  (other: read T): Bool -> this.cmp(this.close, other,{.lt ->True;.eq ->False; .gt -> True});

  read <=>[R:**](other: read Order[T], m: mut OrderMatch[R]): R -> this.cmp(this.close, other.close, m);
}
OrderBy[T,K]:{
  #(read T): read Order[K];
  .then[K0](next: OrderBy[T,K0]): OrderBy[T] -> {
    .cmp(t0,t1,m)-> this#t0 <=>
      (this#t1, {.lt->m.lt; .gt->m.gt; .eq->next#t0<=>(next#t1,m);})
  };
  .view[A](f:F[read A,read T]):OrderBy[A] ->
    {a0,a1,m-> this#(f#a0)<=>(this#(f#a1),m)};
}
OrderBy[T]:OrderBy[T,T]{
  .cmp[R:**](t0:read T,t1:read T,m:mut OrderMatch[R]): R;
  # t -> { .close -> t; .cmp t0,t1,m -> this.cmp(t0,t1,m) };
}
Order[T,E:*]:{
  read .close:read T;
  read .cmp[K,R:**](by: OrderBy[imm E,K], t0:read T,t1:read T, m: mut OrderMatch[R]): R;
  read .order[K](by: OrderBy[imm E,K]): read Order[T] -> {
    .close -> this.close;
    .cmp t0,t1,m -> this.cmp(by,t0,t1,m);
  };
}
Hasher: {
  mut #[A,B](a: read OrderHash[A], b: read OrderHash[B]): Nat -> a.hash(this) * 31 + (b.hash(this));
}
OrderHash[T]:Order[T],ToStr{ read .hash(h: mut Hasher): Nat }
OrderHash[T,E:*]:Order[T,E],ToStr[E]{
  read .hash[K](by: OrderHashBy[imm E,K], h: mut Hasher): Nat;
  read .orderHash[K](by: OrderHashBy[imm E,K]): read OrderHash[T] -> {
    .close -> this.close;
    .cmp t0,t1,m -> this.cmp(by,t0,t1,m);
    .hash h -> this.hash(by,h);
    .str  -> this.str by;
  };
}
OrderHashBy[T,K]:OrderBy[T,K],ToStrBy[T]{
  #(t:read T): read OrderHash[K];
  .thenHash[K0](next: OrderHashBy[T,K0]): OrderHashBy[T] -> {
    .cmp t0,t1,m -> this#t0<=>(this#t1,{
      .lt ->m.lt;
      .eq ->next#t0<=>(next#t1,m);
      .gt ->m.gt});
    .hash t,h -> h#(this#t, next#t);
  };
  .viewHash[A](f:F[read A,read T]):OrderHashBy[A] -> {
    .cmp a0,a1,m -> this#(f#a0)<=>(this#(f#a1),m);
    .hash a,h -> this#(f#a).hash(h);
  };
}
OrderHashBy[T]:OrderHashBy[T,T]{
  .cmp[R:**](t0:read T,t1:read T,m:mut OrderMatch[R]): R;
  .hash(t: read T,h: mut Hasher):Nat;
  # t -> {
    .close -> t;
    .cmp t0,t1,m -> this.cmp(t0,t1,m);
    .hash h -> this.hash(t,h);
    .str -> this#t.str;
  };
}
Box[E:*]: OrderHash[Box[E],E]{
  mut  .get: E;
  read .get: read/imm E;
  imm  .get: imm E;
  .close->this;
  .cmp by, t0, t1, m-> by#(t0.get)<=>(by#(t1.get),m);
  .hash by, h -> by#(this.get).hash h;
  .str by->by#(this.get).str;
  .proofConcrete(s:Str):Box[Str]->Box[Str]{ .get->s; };//this also tests good handling of RC overloading
}
A1:OrderHash[A1]{
  .close -> this;
  .cmp t0, t1, m -> m.eq;
  .hash h -> 0;
  .str ->Str;
  .proofConcrete:A1->A1;
}
Top:{
  .m00(b:Box[A1]):Bool -> b.order{::} == b;
  .m01(b:Box[read A1]):Bool -> b.order{::} == b;
  .m02(b:Box[mut A1]):Bool -> b.order{::} == b;
  .m03(b:read Box[A1]):Bool -> b.order{::} == b;
  .m04(b:read Box[read A1]):Bool -> b.order{::} == b;
  .m05(b:read Box[mut A1]):Bool -> b.order{::} == b;
  .m06(b:mut Box[A1]):Bool -> b.order{::} == b;
  .m07(b:mut Box[read A1]):Bool -> b.order{::} == b;
  .m08(b:mut Box[mut A1]):Bool -> b.order{::} == b;
  .m09(b1:iso Box[A1],b2:iso Box[A1]):Bool -> b1.order{::} == b2;
  .m10(b1:iso Box[read A1],b2:iso Box[read A1]):Bool -> b1.order{::} == b2;
  .m11(b1:iso Box[mut A1],b2:iso Box[mut A1]):Bool -> b1.order{::} == b2;
  .m12(b:readH Box[A1]):Bool -> b.order{::} == b;
  .m13(b:readH Box[read A1]):Bool -> b.order{::} == b;
  .m14(b:readH Box[mut A1]):Bool -> b.order{::} == b;
  .m15(b:mutH Box[A1]):Bool -> b.order{::} == b;
  .m16(b:mutH Box[read A1]):Bool -> b.order{::} == b;
  .m17(b:mutH Box[mut A1]):Bool -> b.order{::} == b;
  }
ThenHashBoxAll:{
  .thA_A(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  .thR_R(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  .thM_M(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1],h:mut Hasher):Nat -> o.thenHash(p)#x.hash(h);
  }
ThenHashLeBoxAll:{
  .leA_A(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1],y:read Box[A1]):Bool ->
    o.thenHash(p)#x <= y;
  .leR_R(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1],y:read Box[read A1]):Bool ->
    o.thenHash(p)#x <= y;
  .leM_M(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1],y:read Box[mut A1]):Bool ->
    o.thenHash(p)#x <= y;
  }
ThenLeSelf:{
  .leA(o:OrderHashBy[Box[A1]],p:OrderHashBy[Box[A1]],x:read Box[A1]):Bool -> o.then(p)#x <= x;
  .leR(o:OrderHashBy[Box[read A1]],p:OrderHashBy[Box[read A1]],x:read Box[read A1]):Bool -> o.then(p)#x <= x;
  .leM(o:OrderHashBy[Box[mut A1]],p:OrderHashBy[Box[mut A1]],x:read Box[mut A1]):Bool -> o.then(p)#x <= x;
}
ViewBoxAll18:{
  .v00(by:OrderBy[A1],b:Box[A1],c:Box[A1]):Bool -> by.view({x->x.get})#b <= c;
  .v01(by:OrderBy[A1],b:read Box[A1],c:read Box[A1]):Bool -> by.view{x->x.get}#b <= c;
  .v02(by:OrderBy[A1],b:mut Box[A1],c:mut Box[A1]):Bool -> by.view{::.get}#b <= c;
  .v03(by:OrderBy[A1],b1:iso Box[A1],b2:iso Box[A1]):Bool -> by.view({x->x.get})#b1 == b2;
  .v04(by:OrderBy[A1],b:readH Box[A1],c:readH Box[A1]):Bool -> by.view({x->x.get})#b != c;
  .v05(by:OrderBy[A1],b:mutH Box[A1],c:mutH Box[A1]):Bool -> by.view({x->x.get})#b >= c;

  .v06(by:OrderBy[A1],b:Box[read A1],c:Box[read A1]):Bool -> by.view({x->x.get})#b > c;
  .v07(by:OrderBy[A1],b:read Box[read A1],c:read Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v08(by:OrderBy[A1],b:mut Box[read A1],c:mut Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v09(by:OrderBy[A1],b1:iso Box[read A1],b2:iso Box[read A1]):Bool -> by.view({x->x.get})#b1 <= b2;
  .v10(by:OrderBy[A1],b:readH Box[read A1],c:readH Box[read A1]):Bool -> by.view({x->x.get})#b <= c;
  .v11(by:OrderBy[A1],b:mutH Box[read A1],c:mutH Box[read A1]):Bool -> by.view({x->x.get})#b <= c;

  .v12(by:OrderBy[A1],b:Box[mut A1],c:Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v13(by:OrderBy[A1],b:read Box[mut A1],c:read Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v14(by:OrderBy[A1],b:mut Box[mut A1],c:mut Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v15(by:OrderBy[A1],b1:iso Box[mut A1],b2:iso Box[mut A1]):Bool -> by.view({x->x.get})#b1 <= b2;
  .v16(by:OrderBy[A1],b:readH Box[mut A1],c:readH Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;
  .v17(by:OrderBy[A1],b:mutH Box[mut A1],c:mutH Box[mut A1]):Bool -> by.view({x->x.get})#b <= c;

  .vh0(by:OrderHashBy[A1],b:readH Box[mut A1],c:readH Box[mut A1]):Bool -> by.viewHash({x->x.get})#b <= c;
  .vh1(by:OrderHashBy[A1],b:mutH Box[mut A1],h:iso Hasher):Nat -> by.viewHash({x->x.get})#b .hash h;
  .vh2(by:OrderHashBy[A1],b:mut Box[mut A1],h:mut Hasher):Nat -> by.viewHash({x->x.get})#b .hash h;
}
Age:OrderHash[Age]{ read .close->this; read .cmp a,b,m->m.eq; read .hash h->0; }
Name:OrderHash[Name]{ read .close->this; read .cmp a,b,m->m.eq; read .hash h->0; }
Person:{ read .age: Age; read .name: Name; }

CompareBy:{
  #[T,K](by:OrderBy[T,K]): OrderBy[T,K] -> by;
}
CompareBy2a[T]:{
  #[K](by:OrderBy[T,K]): OrderBy[T,K] -> by;
}
CompareBy2b[K]:{
  #[T](by:OrderBy[T,K]): OrderBy[T,K] -> by;
}
AndThenTests2:{
  .orderOk0: OrderBy[Person,Age] ->
    {::.age};
  .orderOk1: OrderBy[Person] ->
    CompareBy#{::.age}.then{::.name};
  .max[T](order:OrderBy[Person,T]):Person;
  .orderOk2:Person->this.max(CompareBy#{::.age}.then{::.name});
  .orderOk2a:Person->this.max(CompareBy2a[Person]#{::.age}.then{::.name});
  .orderOk2b:Person->this.max(CompareBy2b[Age]#{::.age}.then{::.name});
  .orderOk3:Person->this.max({::.age}.then{::.name});
  .orderOk4:Person->this.max({::.age});
}
"""));}

@Test void regressionOrderBy(){ok(List.of("""
Str:{}
Age:{}
Person:{ .age: Age; }
G2[A,T]:{
  .g2(A): T;
  .fooStr(s:Str):Str->s; // ok
  .fooA(a:A):A->a; //this used to break inference
  .fooT(t:T):T->t;   //this used to break inference
  .foo2(t:A):A->t;   //this used to break inference
  .fooT(t:T,tt:T):T->t;   //this used to break inference
}
G1[T]:G2[T,T]{ .foo2(t:T):T->t; }//this was always fine
Make:{ .make[A,K](f:G2[A,K]): G1[A] -> Make.make f; }
Tests:{ .ok: G1[Person] -> Make.make{
  .g2(p:Person):Age->p.age;
  }}
"""));}

@Test void regressionBangMatchWorksWithDiffNames(){ok(List.of("""
Str:{}
Boom:{ .msg[R:**](s: Str): R -> Boom.msg(s); }
BoxMatch[E:*,R:**]:{ mut .some(x: E): R; mut .empty: R; }
_Box[E:*]:{
  mut  .match[R:**](m: mut BoxMatch[E, R]): R;
  read .match[R:* ](m: mut BoxMatch[read/imm E, R]): R;
  imm  .match[R:* ](m: mut BoxMatch[imm E, R]): R;

  mut  !: E;
  read !!: read/imm E;
  imm  !!!: imm E;
}
Box[E:*]: _Box[E]{
  .match(m) -> this.match(m);
  ! -> this.match{ .some x -> x; .empty  -> Boom.msg Str; };
  !! -> this.match{ .some x -> x; .empty  -> Boom.msg Str; };
  !!! -> this.match{ .some x -> x; .empty  -> Boom.msg Str; };

}
"""));}

@Test void regressionBangMatch(){ok(List.of("""
Str:{}
Boom:{ .msg[R:**](s: Str): R -> Boom.msg(s); }
BoxMatch[E:*,R:**]:{ mut .some(x: E): R; mut .empty: R; }
_Box[E:*]:{
  mut  .match[R:**](m: mut BoxMatch[E, R]): R;
  read .match[R:* ](m: mut BoxMatch[read/imm E, R]): R;
  imm  .match[R:* ](m: mut BoxMatch[imm E, R]): R;

  mut  !: E;  //with only one of the 3 uncommented it works,
  read !: read/imm E;//with any 2 of them uncommented it fails
  imm  !: imm E;
}
Box[E:*]: _Box[E]{
  .match(m) -> this.match(m);
  ! -> this.match{ .some x -> x; .empty  -> base.Todo!; };
}
"""));}

@Test void slotReadOptAdaptsOnlyTheOpt(){fail("""
003| Slots:{ #[E:*](e: mut Var[mut Opt[E]]): mut Slot[E] -> mut Slot[E:*]:{
004|   mut  .opt: mut Opt[E] -> e.get;
005|   read .opt: read Opt[read/imm E] -> e.get;
   |   -----------------------------------^^^^^^
006|   } }

While inspecting method call ".get" > ".opt" line 5 > "#(_)" line 3
Method ".opt" inside the object literal "mut Slot[_]" (line 3)
is implemented with an expression returning "read Opt[E]".
Method call "read Var[_].get" has type "read Opt[E]" instead of a subtype of "read Opt[read/imm E]".

See inferred typing context below for how type "read Opt[read/imm E]" was introduced: (compression indicated by `-`)
Slots:{#[E:*](e:mut Var[mut Opt[E]]):mut Slot[E]->mut Slot[E:*]:{e.get[mut];e.get[read]}}
""", List.of("""
Opt[E:*]:{}
Var[E:imm,mut,read]:{ read .get: read/imm E; mut .get: E; }
Slots:{ #[E:*](e: mut Var[mut Opt[E]]): mut Slot[E] -> mut Slot[E:*]:{
  mut  .opt: mut Opt[E] -> e.get;
  read .opt: read Opt[read/imm E] -> e.get;
  } }
"""));}
@Test void slotReadOpt(){ok(List.of("""
Opt[E:*]:{}
Var[E:imm,mut,read]:{ read .get: read/imm E; mut .get: E; }
Slots:{ #[E:*](e: mut Var[mut Opt[E]]): mut Slot[E] -> mut Slot[E:*]:{
  mut  .opt: mut Opt[E] -> e.get;
  read .opt: read Opt[E] -> e.get;
  } }
"""));}
@Test void slotReadOptFresh(){ok(List.of("""
Opt[E:*]:{ read .mapSome[R:*](f: mut F[read/imm E, R]): mut Opt[R]; }
F[A:*,R:*]:{ mut #(a: A): R; }
Var[E:imm,mut,read]:{ read .get: read/imm E; mut .get: E; }
Slots:{ #[E:*](e: mut Var[mut Opt[E]]): mut Slot[E] -> mut Slot[E:*]:{
  mut  .opt: mut Opt[E] -> e.get;
  read .opt: mut Opt[read/imm E] -> e.get.mapSome{x -> x};
  } }
"""));}
@Test void readOptOfMutNotReadOptOfRead(){fail("""
003| User:{ .u(o: read Opt[mut X]): read Opt[read X] -> o; }
   |        --------------------------------------------^^

While inspecting parameter "o" > ".u(_)" line 3
The body of method ".u(_)" of type declaration "User" is an expression returning "read Opt[mut X]".
Parameter "o" has type "read Opt[mut X]" instead of a subtype of "read Opt[read X]".

See inferred typing context below for how type "read Opt[read X]" was introduced: (compression indicated by `-`)
User:{.u(o:read Opt[mut X]):read Opt[read X]->o}
""", List.of("""
Opt[E:*]:{}
X:{}
User:{ .u(o: read Opt[mut X]): read Opt[read X] -> o; }
"""));}


//----Testing name suggester
@Test void nameSuggester_1(){failExt("""
[###]
Did you mean "FooBar" ?
[###]
""", List.of("""
FooBar:{}
User:{.foo:Foo;}
"""));}

@Test void nameSuggester_2(){failExt("""
[###]
Did you mean "abcDef" ?
[###]
""", List.of("""
A:{}
User:{.foo(abc:A, abcDef:A):A->abcDeee;}
"""));}

@Test void nameSuggester_3(){failExt("""
[###]
Did you mean ".foo2" ?
[###]
""", List.of("""
A:{}
User:{
  .foo1:A->this.foo22;
  .foo2:A;
  .foo3:A;
  }
"""));}

// Missing TypeName

@Test void nameSuggester_4(){failExt("""
[###]
Did you mean "FooBar" ?
[###]
""", List.of("""
FooBar:{}
User:{.foo:FooBaar;}
"""));}

@Test void nameSuggester_5(){failExt("""
[###]
Did you mean "NumExact" ?
[###]
""", List.of("""
NumExact:{}
User:{.foo:Num;}
"""));}

@Test void nameSuggester_6(){failExt("""
[###]
Did you mean "ReadOnly" ?
[###]
""", List.of("""
ReadOnly:{}
User:{.foo:ReadOnyl;}
"""));}

@Test void nameSuggester_7(){failExt("""
[###]
Did you mean "HTTPServer" ?
[###]
""", List.of("""
HTTPServer:{}
User:{.foo:HttpServer;}
"""));}

@Test void nameSuggester_8(){failExt("""
[###]
Did you mean "JSONParser" ?
[###]
""", List.of("""
JSONParser:{}
User:{.foo:JsonParser;}
"""));}

@Test void nameSuggester_9(){failExt("""
[###]
Did you mean "XMLHttpRequest" ?
[###]
""", List.of("""
XMLHttpRequest:{}
User:{.foo:XmlHttpRequest;}
"""));}

@Test void nameSuggester_10(){failExt("""
[###]
Did you mean "URLDecoder" ?
[###]
""", List.of("""
URLDecoder:{}
User:{.foo:UrlDecoder;}
"""));}

@Test void nameSuggester_11(){failExt("""
[###]
Did you mean "ASCIIParser" ?
[###]
""", List.of("""
ASCIIParser:{}
User:{.foo:AsciiParser;}
"""));}

@Test void nameSuggester_12(){failExt("""
[###]
Did you mean "FooBar''''" ?
[###]
""", List.of("""
FooBar'''':{}
User:{.foo:FooBar'';}
"""));}

@Test void nameSuggester_13(){failExt("""
[###]
Did you mean "FooBar" ?
[###]
""", List.of("""
FooBar:{}
User:{.foo:Bar;}
"""));}

// Missing .methName

@Test void nameSuggester_14(){failExt("""
[###]
Did you mean ".numExact" ?
[###]
""", List.of("""
A:{}
User:{
  .numExact:A;
  .go:A->this.num;
  }
"""));}

@Test void nameSuggester_15(){failExt("""
[###]
Did you mean ".toJSON" ?
[###]
""", List.of("""
A:{}
User:{
  .toJSON:A;
  .go:A->this.toJson;
  }
"""));}

@Test void nameSuggester_16(){failExt("""
[###]
Did you mean ".parseXML" ?
[###]
""", List.of("""
A:{}
User:{
  .parseXML:A;
  .go:A->this.parseXml;
  }
"""));}

@Test void nameSuggester_17(){failExt("""
[###]
Did you mean ".myHttpServer" ?
[###]
""", List.of("""
A:{}
User:{
  .myHttpServer:A;
  .go:A->this.myHTTPServer;
  }
"""));}

@Test void nameSuggester_18(){failExt("""
[###]
Did you mean ".sha256" ?
[###]
""", List.of("""
A:{}
User:{
  .sha256:A;
  .go:A->this.sha265;
  }
"""));}

@Test void nameSuggester_19(){failExt("""
[###]
Did you mean ".foo'''''" ?
[###]
""", List.of("""
A:{}
User:{
  .foo''''':A;
  .go:A->this.foo'';
  }
"""));}

@Test void nameSuggester_20(){failExt("""
[###]
Did you mean ".readOnly" ?
[###]
""", List.of("""
A:{}
User:{
  .readOnly:A;
  .go:A->this.read;
  }
"""));}

@Test void nameSuggester_21(){failExt("""
[###]
Did you mean ".makeUUID" ?
[###]
""", List.of("""
A:{}
User:{
  .makeUUID:A;
  .go:A->this.makeUuid;
  }
"""));}

@Test void nameSuggester_22(){failExt("""
[###]
Did you mean ".asUTF8" ?
[###]
""", List.of("""
A:{}
User:{
  .asUTF8:A;
  .go:A->this.asUtf8;
  }
"""));}

@Test void nameSuggester_23(){failExt("""
[###]
Did you mean ".xmlHttpRequest" ?
[###]
""", List.of("""
A:{}
User:{
  .xmlHttpRequest:A;
  .go:A->this.xmlHTTPRequest;
  }
"""));}

// Missing parName

@Test void nameSuggester_24(){failExt("""
[###]
Did you mean "numExact" ?
[###]
""", List.of("""
A:{}
User:{.f(numExact:A):A->num;}
"""));}

@Test void nameSuggester_25(){failExt("""
[###]
Did you mean "toJSON" ?
[###]
""", List.of("""
A:{}
User:{.f(toJSON:A):A->toJson;}
"""));}

@Test void nameSuggester_26(){failExt("""
[###]
Did you mean "httpServer" ?
[###]
""", List.of("""
A:{}
User:{.f(httpServer:A):A->myHttpServer;}
"""));}

@Test void nameSuggester_27(){failExt("""
[###]
Did you mean "x'''''" ?
[###]
""", List.of("""
A:{}
User:{.f(x''''':A):A->x'';}
"""));}

@Test void nameSuggester_28(){failExt("""
[###]
Did you mean "byteBuffer" ?
[###]
""", List.of("""
A:{}
User:{.f(byteBuffer:A):A->buffer;}
"""));}

@Test void nameSuggester_29(){failExt("""
[###]
Did you mean "fooBarBaz" ?
[###]
""", List.of("""
A:{}
User:{.f(fooBarBaz:A):A->fooBarBax;}
"""));}

@Test void nameSuggester_30(){failExt("""
[###]
Did you mean "length" ?
[###]
""", List.of("""
A:{}
User:{.f(length:A):A->lenght;}
"""));}

@Test void nameSuggester_31(){failExt("""
[###]
Did you mean "sha256" ?
[###]
""", List.of("""
A:{}
User:{.f(sha256:A):A->sha265;}
"""));}

@Test void nameSuggester_32(){failExt("""
[###]
Did you mean "fooBar" ?
[###]
""", List.of("""
A:{}
User:{.f(fooBar:A):A->myFooBar;}
"""));}

@Test void nameSuggester_33(){failExt("""
[###]
Did you mean "httpServerPort" ?
[###]
""", List.of("""
A:{}
User:{.f(httpServerPort:A):A->serverPort;}
"""));}
@Test void genHeadReported(){fail("""
004| User:{.f(c:C[A]):C[B]->c;}
   |       -----------------^^

While inspecting parameter "c" > ".f(_)" line 4
The body of method ".f(_)" of type declaration "User" is an expression returning "C[A]".
Parameter "c" has type "C[A]" instead of a subtype of "C[B]".

See inferred typing context below for how type "C[B]" was introduced: (compression indicated by `-`)
User:{.f(c:C[A]):C[B]->c}
""", List.of("""
A:{}
B:{}
C[X]:{}
User:{.f(c:C[A]):C[B]->c;}
"""));}
@Test void genHeadReportedObjLit(){fail("""
004| User:{.f(c:C[A]):C[B]->C[A]{ .foo:A->A };}
   |       -----------------^^---------------

While inspecting object literal instance of "C[A]" > ".f(_)" line 4
The body of method ".f(_)" of type declaration "User" is an expression returning "iso C[A]".
Object literal is of type "iso C[A]" instead of a subtype of "C[B]".

See inferred typing context below for how type "C[B]" was introduced: (compression indicated by `-`)
User:{.f(c:C[A]):C[B]->C[A]{.foo:A->A}}
""", List.of("""
A:{}
B:{}
C[X]:{}
User:{.f(c:C[A]):C[B]->C[A]{ .foo:A->A };}
"""));}

@Test void badImplementsVoid(){ failExt("""
In file: [###].fear

006|   imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{ .foo(s:Sup):Sup->s } }
   |                                            ^^^^^^^^^^

While inspecting object literal instance of "base.Void"
Object literal instance of "base.Void" implements sealed type "base.Void".
Sealed types can only be implemented in their own package.
Object literal instance of "base.Void" is in package "p".
Type "base.Void" is in package "base".
Error 7 WellFormedness
""", List.of("""
Sup:{
  imm .h:base.Void;
  imm .k:base.Void;
}
User:{
  imm .m():Sup->Bad:Sup{ imm .h:base.Void->base.Void{ .foo(s:Sup):Sup->s } }
}
"""));}

@Test void badImplicit(){ failExt("""
In file: [###].fear

003| User:Sup{ :: }
   |           ^^

While inspecting parameter "::" > ".h(_)" line 3
The body of method ".h(_)" of type declaration "User" is an expression returning "Sup".
Parameter "::" has type "Sup" instead of a subtype of "base.Void".

See inferred typing context below for how type "base.Void" was introduced: (compression indicated by `-`)
User:Sup{.h(_aimpl:Sup):-.Void->::}
Error 8 TypeError
""", List.of("""

Sup:{ imm .h(x:Sup):base.Void; }
User:Sup{ :: }
"""));}

@Test void badSealed1(){ failExt("""
In file: [###].fear

001| ExtStr:"beer"{}
   | ^^^^^^^^^^^^^^^

While inspecting type declaration "ExtStr"
Type declaration "ExtStr" implements sealed type `"beer"`.
Sealed types can only be implemented in their own package.
Type declaration "ExtStr" is in package "p".
Type `"beer"` is in package "base".
Error 7 WellFormedness
""", List.of("""
ExtStr:"beer"{}
"""));}

@Test void tsWidenAnonLiteralHeadVsRequiredType(){fail("""
003| B:{.m:Target->Sup{}}
   |    -----------^^^^-

While inspecting object literal instance of "Sup" > ".m" line 3
The body of method ".m" of type declaration "B" is an expression returning "iso Sup".
Object literal is of type "Sup" instead of a subtype of "Target".

See inferred typing context below for how type "Target" was introduced: (compression indicated by `-`)
B:{.m:Target->Sup}
""", List.of("""
Sup:base.WidenTo[Target]{}
Target:Sup{}
B:{.m:Target->Sup{}}
"""));}

@Test void tsWidenAnonLiteralHeadControlNoWiden(){fail("""
003| B:{.m:Target->Sup{}}
   |    -----------^^^^-

While inspecting object literal instance of "Sup" > ".m" line 3
The body of method ".m" of type declaration "B" is an expression returning "iso Sup".
Object literal is of type "Sup" instead of a subtype of "Target".

See inferred typing context below for how type "Target" was introduced: (compression indicated by `-`)
B:{.m:Target->Sup}
""", List.of("""
Sup:{}
Target:Sup{}
B:{.m:Target->Sup{}}
"""));}

@Test void tsWidenAnonLiteralHeadMissingMethod(){fail("""
003| B:{.m:Target->Sup{.foo->base.Str}}
   |    -----------^^^^---------------

While inspecting object literal instance of "Sup" > ".m" line 3
The body of method ".m" of type declaration "B" is an expression returning "iso Sup".
Object literal is of type "iso Sup" instead of a subtype of "Target".

See inferred typing context below for how type "Target" was introduced: (compression indicated by `-`)
B:{.m:Target->Sup{.foo:-.Str->-.Str}}
""", List.of("""
Sup:base.WidenTo[Target]{ .foo:base.Str }
Target:Sup{ .extra:base.Str }
B:{.m:Target->Sup{.foo->base.Str}}
"""));}

@Test void tsWidenNamedLiteralBody(){ok(List.of("""
Target:{ .foo(x:Target):Target }
Sup:{ .foo(x:base.Str):base.Str }
B:{ .m:Sup-> N:Sup,base.WidenTo[Target]{ .foo(x)->x } }
"""));}

@Test void tsWidenNamedLiteralBodyControlNoWiden(){ok(List.of("""
Target:{ .foo(x:Target):Target }
Sup:{ .foo(x:base.Str):base.Str }
B:{ .m:Sup-> N:Sup{ .foo(x)->x } }
"""));}

@Test void tsPromotionChanin(){ok(List.of("""
A:{ imm .a1: mut A; mut .a2: A;}
B:{ .b(a:A):A->a.a1.a2; }
C:{ .c(a:A):A->a.a1; }
D:{}
List[P:*]:{read .flow : mut Flow[P]; }
Flow[P:*]:{mut .map(read D): mut Flow[P]; mut .list:mut List[P]}
Names1:{ #(ps: List[A]): iso List[A] -> ps.flow.map iso D{}.list }
Names2:{ #(ps: List[A]): iso List[A] -> ps.flow.map {}.list }
"""));}

@Test void baseIdIdentity(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .m: base.BaseId[Customer,Person] -> {::} }
"""));}
@Test void baseIdIdentityNamed(){ok(List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{ #(x)->x }
"""));}
@Test void baseIdAsCall(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: base.MList[Customer]): base.MList[Person] -> cs.as{::} }
"""));}
@Test void baseIdAsCallExplicitTarg(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: base.MList[Customer]): base.MList[Person] -> cs.as[Person]{::} }
"""));}
@Test void baseIdNested(){ok(List.of("""
Person:{}
Customer:Person{}
User:{
  .m: base.BaseId[base.MList[Customer],base.MList[Person]] -> {::.as{::}};
  .n(css: base.MList[base.MList[Customer]]): base.MList[base.MList[Person]] -> css.as{::.as{::}};
  }
"""));}
@Test void baseIdAsImmListOfMutElements(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: base.MList[mut Customer]): base.MList[Person] -> cs.as{::} }
"""));}
@Test void baseIdAsNestedImmListsOfMutElements(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(css: base.MList[mut base.MList[mut Customer]]): base.MList[base.MList[Person]] -> css.as{::.as{::}} }
"""));}
@Test void baseIdAsMutList(){ok(List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: mut base.MList[Customer]): base.MList[Person] -> cs.as{::} }
"""));}
@Test void baseIdAsReadListOfMutElements(){fail("""
003| User:{ .n(cs: read base.MList[mut Customer]): base.MList[Person] -> cs.as{::} }
   |        -------------------------------------------------------------------^^^

While inspecting parameter "::" > "#(_)" line 3 > ".n(_)" line 3
Method "#(_)" inside the object literal instance of "iso base.BaseId[read Customer,Person]" (line 3)
is implemented with an expression returning "read Customer".
Parameter "::" has type "read Customer" instead of a subtype of "Person".

See inferred typing context below for how type "Person" was introduced: (compression indicated by `-`)
User:{.n(cs:read -.MList[mut Customer]):-.MList[Person]->cs.as[read,Person](-.BaseId[read Customer,Person]{(-)->::})}
""", List.of("""
Person:{}
Customer:Person{}
User:{ .n(cs: read base.MList[mut Customer]): base.MList[Person] -> cs.as{::} }
"""));}
@Test void baseIdProofKeepsTheTypeOfTheArgument(){ok(List.of("""
Person:{}
Customer:Person{ .n: base.Void }
Box[T]:{ .get: T }
Boxes:{ #[T](x: T, f: base.BaseId[T,Person]): Box[T] -> Boxes#(x,f) }
User:{ .m(c: Customer): base.Void -> Boxes#(c,{::}).get.n }
"""));}
@Test void inferenceKeepsTheTypeOfTheArgumentWithoutALiteral(){ok(List.of("""
Person:{}
Customer:Person{ .n: base.Void }
Box[T]:{ .get: T }
Boxes:{ #[T](x: T): Box[T] -> Boxes#x }
User:{ .m(c: Customer): base.Void -> Boxes#(c).get.n }
"""));}
@Test void inferenceKeepsTheTypeOfTheArgumentWithALambda(){ok(List.of("""
Person:{}
Customer:Person{ .n: base.Void }
Box[T]:{ .get: T }
Fn[A,B]:{ #(a: A): B }
Boxes:{ #[T](x: T, f: Fn[T,Person]): Box[T] -> Boxes#(x,f) }
User:{ .m(c: Customer): base.Void -> Boxes#(c,{x -> x}).get.n }
"""));}
@Test void baseIdNotSubtype(){fail("""
003| User:{ .m: base.BaseId[Person,Customer] -> {::} }
   |        -------------------------------------^^^

While inspecting parameter "::" > "#(_)" line 3 > ".m" line 3
Method "#(_)" inside the object literal instance of "iso base.BaseId[Person,Customer]" (line 3)
is implemented with an expression returning "Person".
Parameter "::" has type "Person" instead of a subtype of "Customer".

See inferred typing context below for how type "Customer" was introduced: (compression indicated by `-`)
User:{.m:-.BaseId[Person,Customer]->-.BaseId[Person,Customer]{#(_aimpl:Person):Customer->::}}
""", List.of("""
Person:{}
Customer:Person{}
User:{ .m: base.BaseId[Person,Customer] -> {::} }
"""));}
@Test void baseIdNotIdentity(){fail("""
003| MyId:base.BaseId[Customer,Person]{ #(x)->Person }
   |                                          ^^^^^^

While inspecting the file
Type declaration "MyId" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Compressed relevant code with inferred types: (compression indicated by `-`)
Person
""", List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{ #(x)->Person }
"""));}
@Test void baseIdWrongReceiver(){fail("""
004| MyId:base.BaseId[base.MList[Customer],base.MList[Person]]{ #(x)->Other.cs.as{::} }
   |                                                                  ^^^^^^^^^^^^^^^

While inspecting the file
Type declaration "MyId" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Compressed relevant code with inferred types: (compression indicated by `-`)
Other.cs.as[imm,Person](-.BaseId[Customer,Person]{#(_aimpl:Customer):Person->::})
""", List.of("""
Person:{}
Customer:Person{}
Other:{ .cs: base.MList[Customer] -> base.Nope! }
MyId:base.BaseId[base.MList[Customer],base.MList[Person]]{ #(x)->Other.cs.as{::} }
"""));}
@Test void baseIdAbstractAlias(){ok(List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{}
User:{ .m: MyId -> MyId{::} }
"""));}
@Test void baseIdExtraMethod(){failExt("""
In file: [###].fear

003| MyId:base.BaseId[Customer,Person]{ #(x)->x; .extra: Person -> Person }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyId"
Type declaration "MyId" implements "base.BaseId[_,_]".
Only the method "#(_)" can be declared or inherited here.
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{ #(x)->x; .extra: Person -> Person }
"""));}
@Test void baseIdInheritedNonIdentityBody(){failExt("""
In file: [###].fear

004| MyId:base.BaseId[Customer,Person], Forge{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyId"
Type declaration "MyId" implements "base.BaseId[_,_]".
It inherits the implementation of "#(_)" from "Forge", which does not implement "base.BaseId[_,_]".
Method "#(_)" must be implemented here, or inherited from a type implementing "base.BaseId[_,_]".
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:{}
Forge:{ #(x: Customer): Person -> Person }
MyId:base.BaseId[Customer,Person], Forge{}
User:{ .n(cs: base.MList[Customer]): base.MList[Person] -> cs.as(MyId) }
"""));}
@Test void baseIdInheritedNonIdentityBodyViaAlias(){failExt("""
In file: [###].fear

005| Sub:MyId, Forge{}
   | ^^^^^^^^^^^^^^^^^

While inspecting type declaration "Sub"
Type declaration "Sub" implements "base.BaseId[_,_]".
It inherits the implementation of "#(_)" from "Forge", which does not implement "base.BaseId[_,_]".
Method "#(_)" must be implemented here, or inherited from a type implementing "base.BaseId[_,_]".
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:{}
Forge:{ #(x: Customer): Person -> Person }
MyId:base.BaseId[Customer,Person]{}
Sub:MyId, Forge{}
"""));}
@Test void baseIdInheritedExtraMethod(){failExt("""
In file: [###].fear

004| MyId:base.BaseId[Customer,Person], Extra{ #(x)->x }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "MyId"
Type declaration "MyId" implements "base.BaseId[_,_]".
Only the method "#(_)" can be declared or inherited here.
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:Person{}
Extra:{ .extra: Person }
MyId:base.BaseId[Customer,Person], Extra{ #(x)->x }
"""));}
@Test void baseIdLambdaExtraMethod(){failExt("""
In file: [###].fear

003| User:{ .m: base.BaseId[Customer,Person] -> {#(x)->x; .extra: Person -> Person} }
   |                                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.BaseId[_,_]"
Object literal instance of "base.BaseId[_,_]" implements "base.BaseId[_,_]".
Only the method "#(_)" can be declared or inherited here.
Error 7 WellFormedness""", List.of("""
Person:{}
Customer:Person{}
User:{ .m: base.BaseId[Customer,Person] -> {#(x)->x; .extra: Person -> Person} }
"""));}
@Test void baseIdInheritedFromBaseId(){ok(List.of("""
Person:{}
Customer:Person{}
MyId:base.BaseId[Customer,Person]{ #(x)->x }
Sub:MyId{}
User:{ .n(cs: base.MList[Customer]): base.MList[Person] -> cs.as(Sub) }
"""));}
@Test void eqSugarNameSameAsFreshName(){ok(List.of("""
User:{ .u(n: base.Nat): base.Nat -> base.Block#.let _aeqS = {n}.return{_aeqS} }
"""));}
@Test void eqSugarNameSameAsFreshDestructName(){ok(List.of("""
Pt:{ .x: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u({.x,.y}1: Pt): base.Nat -> base.Block#.let _adiv = {x1}.return{_adiv + y1} }
"""));}
@Test void eqSugarNameSameAsFreshImplicitName(){ok(List.of("""
User:{ .u(n: base.Nat): base.F[base.Nat,base.Nat] -> base.Block#.let _aimpl = {n}.return{ {:: + _aimpl} } }
"""));}
@Test void eqSugarDestructNamesSameAsFreshName(){ok(List.of("""
Pt:{ ._aeqS: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u(p: Pt): base.Nat -> base.Block#.let {._aeqS,.y} = {p}.return{_aeqS + y} }
"""));}
@Test void eqSugarDestructNamesSameAsFreshDestructName(){ok(List.of("""
Pt:{ ._adiv: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u(p: Pt): base.Nat -> base.Block#.let {._adiv,.y}1 = {p}.let {._adiv} = {p}.return{_adiv1 + y1 + _adiv} }
"""));}
@Test void destructParameterWithHygienicResult(){ok(List.of("""
Pt:{ .x: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u[R:**]({.x,.y}1: Pt, f: mut base.MF[base.Nat,base.Nat,R]): R -> f#(x1,y1) }
"""));}
@Test void destructParametersMoreThanFourNames(){ok(List.of("""
P3:{ .a: base.Nat -> 1; .b: base.Nat -> 2; .c: base.Nat -> 3 }
User:{ .u({.a,.b,.c}1: P3, {.a,.b,.c}2: P3): base.Nat -> a1 + b1 + c1 + a2 + b2 + c2 }
"""));}
@Test void destructParameterNamesSameAsFreshName(){ok(List.of("""
Pt:{ ._aeqS: base.Nat -> 1; .y: base.Nat -> 2 }
User:{ .u({._aeqS,.y}: Pt): base.Nat -> base.Block#.let z = {y}.return{_aeqS + z} }
"""));}


@Test void oldStyleAsMapsFine(){ok(List.of("""
Person:{ .name: base.Str }
MFList[E:*]: { imm .as[R](f: base.MF[imm E,R]): MFList[R] -> base.Nope! }
User:{ .n(ps: MFList[Person]): MFList[base.Str] -> ps.as{::.name} }
"""));}
@Test void oldStyleAsIdentityFine(){ok(List.of("""
Person:{}
Customer:Person{}
MFList[E:*]: { imm .as[R](f: base.MF[imm E,R]): MFList[R] -> base.Nope! }
User:{ .n(cs: MFList[Customer]): MFList[Customer] -> cs.as{::} }
"""));}
@Test void oldStyleAsWidens(){ok(List.of("""
Person:{}
Customer:Person{}
MFList[E:*]: { imm .as[R](f: base.MF[imm E,R]): MFList[R] -> base.Nope! }
User:{ .n(cs: MFList[Customer]): MFList[Person] -> cs.as{::} }
"""));}
@Test void oldStyleAsWidensWithExplicitTarg(){ok(List.of("""
Person:{}
Customer:Person{}
MFList[E:*]: { imm .as[R](f: base.MF[imm E,R]): MFList[R] -> base.Nope! }
User:{ .n(cs: MFList[Customer]): MFList[Person] -> cs.as[Person]{::} }
"""));}
@Test void expectedTypeDecidesTypeArgument(){ok(List.of("""
Person:{}
Customer:Person{}
Box[E:*]:{}
Boxes:{ #[E:*](e: E): Box[E] -> {} }
User:{ .m(c: Customer): Box[Person] -> Boxes#c }
"""));}
@Test void expectedTypeDecidesTypeArgumentOverJoin(){ok(List.of("""
Animal:{}
Dog:Animal{}
Rex:Dog{}
Fido:Dog{}
Pair[E:*]:{}
Pairs:{ #[E:*](a: E, b: E): Pair[E] -> {} }
User:{ .m: Pair[Animal] -> Pairs#(Rex, Fido) }
"""));}
@Test void expectedTypeDecidesTypeArgumentOverNamedLiterals(){ok(List.of("""
Animal:{}
Dog:Animal{}
Pair[E:*]:{}
Pairs:{ #[E:*](a: E, b: E): Pair[E] -> {} }
User:{ .m: Pair[Animal] -> Pairs#(Rex:Dog{}, Fido:Dog{}) }
"""));}
@Test void expectedTypeDecidesTypeArgumentOverWidenTo(){ok(List.of("""
Box[E:*]:{}
Boxes:{ #[E:*](e: E): Box[E] -> {} }
Family[T]:base.WidenTo[T]{}
Dir:Family[Dir]{}
North:Dir{}
User:{ .m: Box[Family[Dir]] -> Boxes#North }
"""));}
@Test void expectedTypeDecidesNestedTypeArguments(){ok(List.of("""
Person:{}
Customer:Person{}
Box[E:*]:{}
Boxes:{ #[E:*](e: E): Box[E] -> {} }
User:{ .m(c: Customer): Box[Box[Person]] -> Boxes#(Boxes#c) }
"""));}
@Test void expectedSupertypeDecidesTypeArgument(){ok(List.of("""
Person:{}
Customer:Person{}
Sup[E:*]:{}
Box[E:*]:Sup[E]{}
Boxes:{ #[E:*](e: E): Box[E] -> {} }
User:{ .m(c: Customer): Sup[Person] -> Boxes#c }
"""));}
@Test void emptyLiteralTakesSelfArgument(){ok(List.of("""
Closed[T]:{ read .close: read T }
A:Closed[A]{ .close->this }
Need:{ #(c: read Closed[A]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralTakesSelfArgumentAmongTwo(){ok(List.of("""
Closed[T,E:*]:{ read .close: read T }
Box[E:*]:Closed[Box[E],E]{ .close->this }
Need:{ #[E:*](c: read Closed[Box[E],E], e: E): Need -> this }
User:{ .m: Need -> Need#({}, User) }
"""));}
@Test void emptyLiteralTakesRepeatedSelfArgument(){ok(List.of("""
Closed[T,E]:{ read .close: read T }
A:Closed[A,A]{ .close->this }
Need:{ #(c: read Closed[A,A]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralTakesSelfArgumentAfterWiderResult(){ok(List.of("""
Sup:{}
Closed[T]:Sup{ read .close: read T }
A:Closed[A]{ .close->this }
Ids:{ #[X](a: X, b: X): X -> a }
User:{ .m(c: Closed[A]): Sup -> Ids#({}, c) }
"""));}
@Test void emptyLiteralKeepsHeadWithOnlyMutAbstract(){ok(List.of("""
Closed[T]:{ mut .close: T }
A:Closed[A]{ .close->A }
Need:{ #(c: Closed[A]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralTakesSelfArgumentTwice(){ok(List.of("""
Closed[T]:{ read .close: read T }
Wrap[T]:Closed[Wrap[T]]{ read .unwrap: read T }
A:Wrap[A]{ .close->this; .unwrap->this }
Need:{ #(c: read Closed[Wrap[A]]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void writtenHeadIsNotSelfArgument(){fail("""
004| User:{ .m: Need -> Need#(Closed[A]{}) }
   |        ------------------^^^^^^^-----

While inspecting object literal instance of "iso Closed[A]" > ".m" line 4
This object literal is missing a required method.
Missing: "read .close".
Required by: "Closed[_]".
Hint: add an implementation for ".close" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso Closed[A]
""", List.of("""
Closed[T]:{ read .close: read T }
A:Closed[A]{ .close->this }
Need:{ #(c: read Closed[A]): Need -> this }
User:{ .m: Need -> Need#(Closed[A]{}) }
"""));}
@Test void emptyLiteralNoSelfArgument(){fail("""
004| User:{ .m: Need -> Need#{} }
   |        -----------------^^

While inspecting object literal instance of "iso Closed[B]" > ".m" line 4
This object literal is missing a required method.
Missing: "read .close".
Required by: "Closed[_]".
Hint: add an implementation for ".close" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso Closed[B]
""", List.of("""
Closed[T]:{ read .close: read T }
B:{}
Need:{ #(c: read Closed[B]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralTwoSelfArguments(){fail("""
005| User:{ .m: Need -> Need#{} }
   |        -----------------^^

While inspecting object literal instance of "iso Closed[A,B]" > ".m" line 5
This object literal is missing a required method.
Missing: "read .close".
Required by: "Closed[_,_]".
Hint: add an implementation for ".close" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso Closed[A,B]
""", List.of("""
Closed[T,E]:{ read .close: read T }
A:Closed[A,B]{ .close->this }
B:Closed[A,B]{ .close->A }
Need:{ #(c: read Closed[A,B]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}
@Test void emptyLiteralSelfArgumentStillAbstract(){fail("""
004| User:{ .m: Need -> Need#{} }
   |        -----------------^^

While inspecting object literal instance of "iso A" > ".m" line 4
This object literal is missing a required method.
Missing: "imm .name".
Required by: "A".
Hint: add an implementation for ".name" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso A
""", List.of("""
Closed[T]:{ read .close: read T }
A:Closed[A]{ .name: A }
Need:{ #(c: read Closed[A]): Need -> this }
User:{ .m: Need -> Need#{} }
"""));}

/*The five tests below are the minimized shapes of every place base stops compiling if
InjectionSteps.nextMStarOp stops meeting a method's declared return type with the type of its
body, that is if
  var ret= meet(m.sig().ret().get(), e.t());
becomes
  var ret= m.sig().ret().get();*/

@Test void blockLetInfersItsTypeFromTheLambdaBody(){ok(List.of("""
use base.MF as MF; use base.Bool as Bool; use base.True as True;
Blocks: { #[R:*]: mut Block[R] -> {} }
Block[R:*]: {
  mut .return(a: mut MF[R]): R -> a#;
  mut .let[X:*](x: mut MF[X], cont: mut Continuation[X,R]): R -> cont#(x#, this);
  }
Continuation[T:*,R:*]: { mut #(x: T, self: mut Block[R]): R }
Amount: { +(o: Amount): Amount -> this; .lt(o: Amount): Bool -> True }
User: {
  .m(a: Amount, b: Amount): Amount -> Blocks#
    .let sum = {a + b}
    .return { sum.lt(b).if {
        .then -> sum + b;
        .else -> sum
      }};
  }
"""));}
/*Minimizes base.Math.euclideanMod in math.fear. "X" of ".let" appears only inside the "mut MF[X]"
parameter, so nothing at the use site can decide it and the lambda body is the only source. The
".if" in the continuation matters: with a plain ".return {sum}" the requirement on the block's own
result reaches "sum" and X is decided anyway; once "sum" is only ever a receiver inside the
continuation, dropping the meet leaves "iso MF[InferUnknown]".*/

@Test void thenElseInfersItsTypeFromTheBranchBodies(){ok(List.of("""
use base.Bool as Bool; use base.Void as Void; use base.Nope as Nope;
Seq: { #[A:**,R:**](a: A, res: R): R -> res }
User: {
  .m[R:iso,imm,mut,read](r: R, b: Bool): R -> Seq#(b?{.then->Void; .else->Nope!}, r);
  }
"""));}
/*Minimizes base._IdOrErr in var.fear. Same reason as the test above but through "?" instead of
".let": "R" of "base.ThenElse[R]" is only the return type of the branches, and "Seq" discards its
first argument, so the branch bodies are the only source of R.*/

@Test void identityLambdaInfersItsKeyTypeFromItsOwnParameter(){ok(List.of("""
use base.Nope as Nope;
Ord[K]: {}
By[T,K]: {
  #(x: read T): read Ord[K];
  .hide: By[T,K] -> this;
  }
Key: Ord[Key] {}
Box[T]: {}
Mk: { #[T,K](by: By[T,K], t: T): Box[T] -> Nope! }
Caller: { .go(x: Key): Box[Key] -> Mk#({::}, x) }
"""));}
/*Minimizes the "Maps#({::},k1,e1.info)" calls of base.Infos in datatypes/info/info.fear. "T" of "By"
comes from the use site, "K" does not: it can only come from the body of "{::}", which is the
parameter of the very method whose return type we are deciding. Dropping the meet leaves the head
of "{::}" at "By[InferUnknown,InferUnknown]" while its method table is refined with "Key", and the
literal is then internally inconsistent: this one fails the "mostSpecificByOrigin" assert inside
TypeSystem.methodTableOk rather than reporting a user error.*/

@Test void blockLetOfAMutResultCannotBePromotedThroughACapturedMut(){fail("""
011|   mut .take(s: mut Set[E], e: E): Opt[E] -> Blocks#
012|     .let o = {s.opt(e)}
013|     .return {o};
   |              ^^

While inspecting parameter "o" > "#" line 13 > "#(_,_)" line 11 > ".take(_,_)" line 11
Method "#" inside the object literal instance of "mut MF[Opt[E]]" (line 13)
is implemented with an expression returning "mut Opt[E]".
Parameter "o" has type "mut Opt[E]" instead of a subtype of "imm Opt[E]".

See inferred typing context below for how type "Opt[E]" was introduced: (compression indicated by `-`)
-.let[mut,mut Opt[E]](-,mut Con-ion[mut Opt[E],Opt[E]]{(-,-)->_aeqS.return[mut](mut MF[Opt[E]]{o})})
""", List.of("""
use base.MF as MF;
Blocks: { #[R:*]: mut Block[R] -> {} }
Block[R:*]: {
  mut .return(a: mut MF[R]): R -> a#;
  mut .let[X:*](x: mut MF[X], cont: mut Continuation[X,R]): R -> cont#(x#, this);
  }
Continuation[T:*,R:*]: { mut #(x: T, self: mut Block[R]): R }
Opt[E:imm]: {}
Set[E:imm]: { mut .opt(e: E): mut Opt[E] -> {} }
User[E:imm]: {
  mut .take(s: mut Set[E], e: E): Opt[E] -> Blocks#
    .let o = {s.opt(e)}
    .return {o};
  }
"""));}

@Test void blockLetTypeCarriesTheClassTypeParameterIntoTheLambda(){ok(List.of("""
use base.MF as MF; use base.Nat as Nat; use base.Ten as Ten;
Blocks: { #[R:*]: mut Block[R] -> {} }
Block[R:*]: {
  mut .return(a: mut MF[R]): R -> a#;
  mut .let[X:*](x: mut MF[X], cont: mut Continuation[X,R]): R -> cont#(x#, this);
  }
Continuation[T:*,R:*]: { mut #(x: T, self: mut Block[R]): R }
Set[E:imm]: { .distinct: Set[E] -> this }
User[E:imm]: {
  .m(other: Set[E]): Nat -> Blocks#
    .let other2 = {other.distinct}
    .return {Ten};
  }
"""));}
/*Minimizes base.Set.difference in datatypes/collections/sets/set.fear. X is again only decided by
the lambda body, but the body's type mentions "E", so the failure is not the one of
blockLetInfersItsTypeFromTheLambdaBody: the literal generated for "{other.distinct}" is given the
head "iso MF[InferUnknown]", which mentions no generic type parameter, so the fresh declaration is created
without binders and capturing "other" is then reported as a capture error.*/


@Test void overridingErrorsAreReportedInDeclarationOrder(){fail("""
004| B: A { .m1: P -> P; .m2: P -> P }
   | -------^^^^^^^^^^^---------------

While inspecting type declaration "B"
Invalid method signature overriding for "B.m1".
The method ".m1" returns type "P".
But "A.m1" returns type "Q", which is not a supertype of "P".
It is instead a subtype: you are weakening the result instead of strengthening it.

Compressed relevant code with inferred types: (compression indicated by `-`)
B:A{.m1:P->P;.m2:P->P}
""", List.of("""
P:{}
Q:P{}
A: { .m1: Q; .m2: Q }
B: A { .m1: P -> P; .m2: P -> P }
"""));}
/*Both ".m1" and ".m2" are bad overrides, and litOk reports whichever method key it visits first.
litOk groups the result of Sources.collect by method key in a LinkedHashMap, so that order is fixed
from run to run. A HashMap keyed on a record holding an RC would not do: enum hashCodes are identity hashCodes, the
order would depend on the JVM's allocation sequence, and an unrelated change elsewhere in the run
would silently change which of the two errors the user is shown.*/

@Test void miniClassDoesntCauseCompilationProblem(){ok(List.of("""
use base.Opt as Opt;
use base.Opts as Opts;
use base.F as F;

TestClass[T]: {
  .opt: mut Opt[T];
  .example[R:*](f: F[R]): mut Opt[R] -> this.opt.match {
    .some _ -> Opts#(f#);
    .empty -> {};
    };
  }
"""));}
@Test void anonLiteralWithRcOverloadsAgainstTypeArgumentWithoutRc(){ok(List.of("""
Foo:{}
Ids:{ #[T:*](t: T): read T -> t }
User:{ .f: read base.Opt[Foo] -> Ids#({ .match m -> m.empty }) }
"""));}
@Test void anonLiteralAgainstTypeArgumentWithoutRc(){ok(List.of("""
Foo:{}
Sup:{ .g: Foo }
Ids:{ #[T:*](t: T): read T -> t }
User:{ .f: read Sup -> Ids#({ .g -> Foo }) }
"""));}
@Test void inferenceLimit_anonLiteralCapturingMutAgainstTypeArgumentWithoutRc(){fail("""
004| User:{ .f(s: mut Sup, c: mut Foo): Foo -> Two#(s, { .run -> c }) }
   |        ---------------------------------------------~~~~~~~~^---

While inspecting parameter "c" > ".run" line 4 > ".f(_,_)" line 4
Parameter "c" has type "mut Foo".
Parameter "c" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "Sup" (line 4).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
c
""", List.of("""
Foo:{}
Sup:{ mut .run: mut Foo }
Two:{ #[T:*](a: mut T, b: T): Foo -> Foo }
User:{ .f(s: mut Sup, c: mut Foo): Foo -> Two#(s, { .run -> c }) }
"""));}
@Test void mutLiteralCapturingMutAgainstTypeArgumentWithoutRc(){ok(List.of("""
Foo:{}
Sup:{ mut .run: mut Foo }
Two:{ #[T:*](a: mut T, b: T): Foo -> Foo }
User:{ .f(s: mut Sup, c: mut Foo): Foo -> Two#(s, mut Sup{ .run -> c }) }
"""));}
@Test void inferenceLimit_anonLiteralWithRcOverloadsCapturingMutAgainstTypeArgumentWithoutRc(){fail("""
004| User:{ .f(s: mut Box, c: mut Foo): Foo -> Two#(s, { .get -> c }) }
   |        ---------------------------------------------~~~~~~~~^---

While inspecting parameter "c" > ".get" line 4 > ".f(_,_)" line 4
Parameter "c" has type "mut Foo".
Parameter "c" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "Box" (line 4).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
c
""", List.of("""
Foo:{}
Box:{ mut .get: mut Foo; read .get: read Foo }
Two:{ #[T:*](a: mut T, b: T): Foo -> Foo }
User:{ .f(s: mut Box, c: mut Foo): Foo -> Two#(s, { .get -> c }) }
"""));}
@Test void mutLiteralWithRcOverloadsCapturingMutAgainstTypeArgumentWithoutRc(){ok(List.of("""
Foo:{}
Box:{ mut .get: mut Foo; read .get: read Foo }
Two:{ #[T:*](a: mut T, b: T): Foo -> Foo }
User:{ .f(s: mut Box, c: mut Foo): Foo -> Two#(s, mut Box{ .get -> c }) }
"""));}
@Test void inferenceLimit_anonLiteralCapturingMutAgainstTypeArgumentFromIsoArgument(){fail("""
004| User:{ .f(s: iso Sup, c: mut Foo): Foo -> Two#(s, { .run -> c }) }
   |        ---------------------------------------------~~~~~~~~^---

While inspecting parameter "c" > ".run" line 4 > ".f(_,_)" line 4
Parameter "c" has type "mut Foo".
Parameter "c" can observe mutation; thus it cannot be captured in the "imm" object literal instance of "Sup" (line 4).
Hint: capture an immutable copy instead, or move this use outside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
c
""", List.of("""
Foo:{}
Sup:{ mut .run: mut Foo }
Two:{ #[T:*](a: T, b: T): Foo -> Foo }
User:{ .f(s: iso Sup, c: mut Foo): Foo -> Two#(s, { .run -> c }) }
"""));}
@Test void mutLiteralCapturingMutAgainstTypeArgumentFromIsoArgument(){ok(List.of("""
Foo:{}
Sup:{ mut .run: mut Foo }
Two:{ #[T:*](a: T, b: T): Foo -> Foo }
User:{ .f(s: iso Sup, c: mut Foo): Foo -> Two#(s, mut Sup{ .run -> c }) }
"""));}

@Test void isoLiteralCanUseItsSelfName(){ok(List.of("""
Counter:{ mut .inc: mut Counter; read .get: base.Nat; mut .inc2: mut Counter }
Make:{ #: iso Counter -> iso Counter{'self
  mut .inc: mut Counter -> self;
  read .get: base.Nat -> 0;
  mut .inc2: mut Counter -> self.inc[mut].inc[mut];
  } }
"""));}
@Test void isoLiteralStillDropsCapturedIso(){ok(List.of("""
A:{}
Box:{ read .get: A; }
Make:{ #(a:iso A): iso Box -> iso Box{ read .get: A -> a } }
"""));}
@Test void isoLiteralSelfIsReadInReadMethod(){fail("""
002| Make:{ #: iso Counter -> iso Counter{'self
003|   mut .inc: mut Counter -> self;
004|   read .get: read Counter -> self.inc[mut];
   |   ---------------------------~~~~^^^^^~~~~~
005|   } }

While inspecting ".get" line 4 > "#" line 2
This call to method "mut Counter.inc" cannot typecheck.
The receiver (the expression before the method name) has capability "read".
This call requires a receiver with capability "mut" or "iso".

Receiver required by each promotion:
- "mut" (As declared)
- "iso" (Strengthen result)

Compressed relevant code with inferred types: (compression indicated by `-`)
self.inc[mut]
""", List.of("""
Counter:{ mut .inc: mut Counter; read .get: read Counter }
Make:{ #: iso Counter -> iso Counter{'self
  mut .inc: mut Counter -> self;
  read .get: read Counter -> self.inc[mut];
  } }
"""));}
@Test void isoLiteralStillPromotesUnnamedMutLiteral(){ok(List.of("""
Counter:{ read .get: base.Nat }
Make:{ #: iso Counter -> mut Counter{ read .get: base.Nat -> 0 } }
"""));}
@Test void isoLiteralPromotesSelfNamedMutLiteral(){ok(List.of("""
Counter:{ mut .inc: mut Counter; read .get: base.Nat }
Make:{ #: iso Counter -> mut Counter{'self
  mut .inc: mut Counter -> self;
  read .get: base.Nat -> 0;
  } }
"""));}
@Test void isoLiteralPromotesSelfNamedImmLiteral(){ok(List.of("""
A:{ read .me: imm A }
Make:{ #: iso A -> imm A{'self read .me: imm A -> self } }
"""));}
@Test void selfNameDeadCode(){fail("""
002| Make:{ #: A -> A{'self read .get: base.Nat -> 0 } }
   |        --------^^--------------------------------

While inspecting object literal instance of "A" > "#" line 2
The self name "self" is dead code.
No method of the object literal instance of "A" uses it.
Remove "'self" from the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
A{'self read .get:-.Nat->0}
""", List.of("""
A:{ read .get: base.Nat }
Make:{ #: A -> A{'self read .get: base.Nat -> 0 } }
"""));}
@Test void selfNameUsedOnlyInNestedLiteral(){ok(List.of("""
A:{ read .get: A }
Make:{ #: A -> A{'self read .get: A -> A{ read .get: A -> self } } }
"""));}
@Test void mutLiteralCapturingIsoIsPromotedToIso(){ok(List.of("""
A:{}
Box:{ read .get: A; }
Make:{ #(a:iso A): iso Box -> mut Box{ read .get: A -> a } }
"""));}
@Test void inheritedMethodSpelledWithAndWithoutRedundantRcOnTypeVariable(){ok(List.of("""
M[R:**]:{ mut .a: R; mut .b: R -> this.a; }
TM[K]:{ read #(x: K): mut M[K] }
MM:{ #[K]: TM[K] -> {x -> { .a -> x }} }
"""));}
@Test void inheritedMethodSpelledWithAndWithoutRedundantMutOnTypeVariable(){ok(List.of("""
M[R:**]:{ mut .a: R; mut .b: R -> this.a; }
TM[K:mut]:{ read #(x: K): mut M[K] }
MM:{ #[K:mut]: TM[K] -> {x -> { .a -> x }} }
"""));}
@Test void lambdaParameterTypedFromExplicitTypeArgumentOfReceiverCall(){ok(List.of("""
Fn[A:*,R:*]:{ read #(a: A): R }
TF[E:*]:{ }
L[E:*]:TF[E]{ }
Fl[E:*]:{ mut .g[R:*](f: read Fn[E, read TF[R]]): mut Fl[R]; }
Fls:{ #[R:*](r: R): mut Fl[R]; }
Use:{ #[E:*](fls: Fls, xs: mut L[E]): mut Fl[E] -> fls#[read TF[E]](xs).g[E]{c -> c} }
"""));}
@Test void explicitTypeArgumentKeepsItsRcAgainstTheArgument(){ok(List.of("""
Fn[A:*,R:*]:{ read #(a: A): R }
TF[E:*]:{ }
Fl[E:*]:{ mut .g[R:*](f: read Fn[E, read TF[R]]): mut Fl[R]; }
Fls:{ #[R:*](r: R): mut Fl[R]; }
Use:{ #[E:*](fls: Fls, xs: mut TF[E]): mut Fl[E] -> fls#[read TF[E]](xs).g[E]{c -> c} }
"""));}
@Test void lambdaParameterTypedFromReceiverTypeWhenReceiverIsParameter(){ok(List.of("""
Fn[A:*,R:*]:{ read #(a: A): R }
TF[E:*]:{ }
L[E:*]:TF[E]{ }
Fl[E:*]:{ mut .g[R:*](f: read Fn[E, read TF[R]]): mut Fl[R]; }
Use:{ #[E:*](fl: mut Fl[read TF[E]]): mut Fl[E] -> fl.g[E]{c -> c} }
"""));}@Test void inferredTypeArgumentOfNestedCallFollowsExpectedType(){ok(List.of("""
C:{}
L[E:*]:{}
Ls:{ #[E:*](e: E): mut L[E] -> {} }
User:{ .nested(css: L[L[C]]): C -> C; .t: C -> this.nested(Ls#(Ls#(C))) }
"""));}
@Test void argFromObjectLiteral_mutHParam_hintToWriteMutLiteral(){fail("""
005|   .f:B->
006|     Need#(read A{});
   |     ----^^-------

While inspecting ".f" line 5
This call to method "Need#(_)" cannot typecheck.
Argument 1 has type "read A".
That is not a subtype of any of "mutH A" or "iso A".
Object literal is of type "read A" instead of a subtype of "mutH A".
Hint: write "mut A" if you need a "mut" object literal (needed to satisfy the "mutH" requirement).

Type required by each promotion:
[###]
""", List.of("""
B:{}
Need:{ #(a:mutH A):B->B{} }
A:{ mut .foo:A}
User:{
  .f:B->
    Need#(read A{});
}
"""));}
@Test void bodyFromObjectLiteral_wrongNominal_noHintToChangeRC(){fail("""
004|   .f:mut A->
005|     read C{};
   |          ^^

While inspecting object literal instance of "read C" > ".f" line 4
The body of method ".f" of type declaration "User" is an expression returning "read C".
Object literal is of type "read C" instead of a subtype of "mut A".

See inferred typing context below for how type "mut A" was introduced: (compression indicated by `-`)
User:{.f:mut A->read C}
""", List.of("""
A:{ mut .foo:A}
C:{ mut .bar:C}
User:{
  .f:mut A->
    read C{};
}
"""));}
@Test void tsWidenRedundantlyListed(){ok(List.of("""
Sup:base.WidenTo[Target]{}
Target:Sup, base.WidenTo[Target]{}
"""));}
@Test void tsWidenRedundantlyListedNested(){ok(List.of("""
Sup:base.WidenTo[Target]{}
Target:Sup{}
User:{ #:Sup->N:base.WidenTo[Target], Sup{} }
"""));}
@Test void tsSupertypesCollapsingUnderInstantiation(){ok(List.of("""
Foo[X:imm]:{}
S:{}
A[X:imm]:Foo[X],Foo[S]{ .m:S; }
User:{ #:A[S]->{ .m->S{} } }
"""));}
@Test void tsSupertypesCollapsingUnderInstantiationSpelledDifferently(){ok(List.of(
  "Foo[X:*]:{} S:{} A[X:*,Y:*]:Foo[X],Foo[Y]{ .m:S; } User:{ #[Z:imm]:A[Z,imm Z]->{ .m->S{} } }"));}
@Test void tsSupertypesCollapsingUnderInstantiationSpelledDifferentlyTyped(){ok(List.of(
  "Foo[X:*]:{} S:{} A[X:*,Y:*]:Foo[X],Foo[Y]{ .m:S; } User:{ #[Z:imm]:A[Z,imm Z]->A[Z,imm Z]{ .m->S{} } }"));}
@Test void tsSupertypesCollapsingUnderInstantiationSpelledDifferentlyReadImm(){ok(List.of(
  "Foo[X:**]:{} S:{} A[X:**,Y:**]:Foo[X],Foo[Y]{ .m:S; } User:{ #[Z:imm]:A[Z,read/imm Z]->{ .m->S{} } }"));}
@Test void nestedSelfDispatchUsesMethodCapability(){ok(List.of("""
A:{ imm .m1: A; mut .m1: mut A; .m2: A }
User:{ #: mut A -> mut B:A{'self .m1 -> self; .m2 -> self.m1 } }
"""));}
@Test void nestedSelfDispatchUsesReadMethodCapability(){ok(List.of("""
A:{ read .m1: read A; mut .m1: mut A; read .m2: read A }
User:{ #: mut A -> mut B:A{'self .m1 -> self; .m2 -> self.m1 } }
"""));}
@Test void nestedSelfCapturedDeeperUsesMethodCapability(){ok(List.of("""
A:{ imm .m1: A; mut .m1: mut A; .m2: mut G }
G:{ mut .get: A }
User:{ #: mut A -> mut B:A{'self .m1 -> self; .m2 -> mut G{ .get -> self.m1 } } }
"""));}
@Test void isoNestedSelfCapturedDeeperIsMut(){ok(List.of("""
A:{ imm .m1: A; mut .m1: mut A; mut .m2: mut G }
G:{ mut .get: mut A }
User:{ #: iso A -> iso B:A{'self .m1 -> self; .m2 -> mut G{ .get -> self.m1 } } }
"""));}
@Test void genericArgumentsJoinToTheSupertype(){ok(List.of("""
A:{} Z:A{}
U:{ .both[T](a: T, b: T): T -> a; .use(a: A, z: Z): A -> this.both(a, z) }
"""));}
@Test void genericArgumentsJoinToTheSupertypeInEitherOrder(){ok(List.of("""
A:{} Z:A{}
U:{ .both[T](a: T, b: T): T -> a; .use(a: A, z: Z): A -> this.both(z, a) }
"""));}
@Test void genericArgumentsJoinMutAndImmToRead(){ok(List.of("""
A:{}
U:{ .both[T:*](a: T, b: T): T -> a; .use(m: mut A, i: imm A): read A -> this.both(m, i) }
"""));}
@Test void genericArgumentFromALiteralJoinsToo(){ok(List.of("""
A:{} Z:A{}
U:{ .app[T](f: base.F[T], x: T): T -> x; .use(a: A, z: Z): A -> this.app({ z }, a) }
"""));}
@Test void siblingsJoinToTheExpectedSupertypeA(){ok(List.of("""
A:{} B:{} Y:A,B{} Z:A,B{}
U:{ .both[T](a: T, b: T): T -> a; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}
@Test void siblingsJoinToTheExpectedSupertypeB(){ok(List.of("""
A:{} B:{} Y:A,B{} Z:A,B{}
U:{ .both[T](a: T, b: T): T -> a; .use(y: Y, z: Z): B -> this.both(y, z) }
"""));}
@Test void siblingsWithoutContextCannotBeInferred(){failWf("""
002| U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
   |                                                          ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
"T" could be "A" or "B": each is a supertype of "Y" and "Z". The choice is ambiguous.
Write the generic type argument explicitly, as in "this.both[A](y, z)".
""", List.of("""
A:{} B:{} Y:A,B{} Z:A,B{}
U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}
@Test void siblingsWithOneCommonSupertypeInferIt(){ok(List.of("""
A:{ .k: A -> this } Y:A{} Z:A{}
U:{ .both[T](a: T, b: T): T -> a; .use(y: Y, z: Z): A -> this.both(y, z).k }
"""));}
@Test void unrelatedTypesCannotBeInferred(){failWf("""
002| U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
   |                                                          ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.both[Type1](y, z)".
""", List.of("""
A:{} Y:{} Z:{}
U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}
@Test void methodBodiesOfUnrelatedTypesCannotBeInferred(){failWf("""
003| U:{ .use(c: base.Bool, y: Y, z: Z): A -> Sink#(c ? { .then -> y; .else -> z }) }
   |                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.ThenElse[_]"
The generic type argument "R" of "base.ThenElse[_]" is inferred from the method bodies, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "base.ThenElse[Type1]{...}".
""", List.of("""
A:{} Y:{} Z:{}
Sink:{ #[T](t: T): A -> A }
U:{ .use(c: base.Bool, y: Y, z: Z): A -> Sink#(c ? { .then -> y; .else -> z }) }
"""));}
@Test void methodBodiesWithTwoCommonSupertypesCannotBeInferred(){failWf("""
003| U:{ .use(c: base.Bool, y: Y, z: Z): A -> Sink#(c ? { .then -> y; .else -> z }) }
   |                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "base.ThenElse[_]"
The generic type argument "R" of "base.ThenElse[_]" is inferred from the method bodies, but they disagree: some need "Y", some need "Z".
"R" could be "S1" or "S2": each is a supertype of "Y" and "Z". The choice is ambiguous.
Write the generic type argument explicitly, as in "base.ThenElse[S1]{...}".
""", List.of("""
A:{} S1:{} S2:{} Y:S1,S2{} Z:S1,S2{}
Sink:{ #[T](t: T): A -> A }
U:{ .use(c: base.Bool, y: Y, z: Z): A -> Sink#(c ? { .then -> y; .else -> z }) }
"""));}
@Test void unconstrainedTypeArgumentInsideATypeArgumentIsVoidWithinItsBound(){ok(List.of("""
Box[X:mut]:{ .k: Box[X] -> this }
Mk:{ #[X:mut]: Box[X] -> Box[X] }
Block:{ #[A](a: A): base.Void -> {} }
User:{ .go: base.Void -> Block#(Mk#) }
"""));}
@Test void unconstrainedTypeArgumentInsideATypeArgumentIsVoidWithinItsReadMutBound(){ok(List.of("""
Box[X:read,mut]:{ .k: Box[X] -> this }
Mk:{ #[X:read,mut]: Box[X] -> Box[X] }
Block:{ #[A](a: A): base.Void -> {} }
User:{ .go: base.Void -> Block#(Mk#) }
"""));}
@Test void emptyLiteralReceiverWithASealedExpectedTypeIsATypeError(){fail("""
001| App:{ .m: base.Nat -> {}.a }
   |       ----------------~~^^

While inspecting ".m" line 1
This call to method ".a" cannot typecheck.
Method ".a" is not declared on "{...}".
Object literal "{...}" does not have any methods.

Compressed relevant code with inferred types: (compression indicated by `-`)
{}.a
""", List.of("""
App:{ .m: base.Nat -> {}.a }
"""));}
@Test void literalReceiverWithAMethodAndASealedExpectedTypeIsATypeError(){fail("""
001| App:{ .m: base.Nat -> {.b:base.Void->base.Void;}.a }
   |       ----------------~~~~~~~~~~~~~~~~~~~~~~~~~~^^

While inspecting ".m" line 1
This call to method ".a" cannot typecheck.
Method ".a" is not declared on "{...}".

Available methods on "{...}":
-       .b:base.Void

Compressed relevant code with inferred types: (compression indicated by `-`)
{.b:-.Void->-.Void}.a
""", List.of("""
App:{ .m: base.Nat -> {.b:base.Void->base.Void;}.a }
"""));}
@Test void typesWithDifferentInvariantArgumentsCannotBeInferred(){failWf("""
002| U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
   |                                                          ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.both[Type1](y, z)".
""", List.of("""
A:{} B:{} Sup[T]:{ .k: T } Y:Sup[A]{ .k -> A } Z:Sup[B]{ .k -> B }
U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}
@Test void aTypeAndASubtypeWithDifferentInvariantArgumentsCannotBeInferred(){failWf("""
002| U:{ .both[T](a: T, b: T): A -> A; .use(y: Sup[A], z: Z): A -> this.both(y, z) }
   |                                                               ^^^^^^^^^^^^^^^

While inspecting method call ".both(_,_)"
The generic type argument "T" of ".both" is inferred from the arguments, but they disagree: some need "Sup[A]", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.both[Type1](y, z)".
""", List.of("""
A:{} B:{} Sup[T]:{ .k: T } Z:Sup[B]{ .k -> B }
U:{ .both[T](a: T, b: T): A -> A; .use(y: Sup[A], z: Z): A -> this.both(y, z) }
"""));}
@Test void typesWithDifferentInvariantArgumentsJoinToACommonSupertypeAbove(){ok(List.of("""
A:{} B:{} Top:{} Sup[T]:Top{ .k: T } Y:Sup[A]{ .k -> A } Z:Sup[B]{ .k -> B }
U:{ .both[T](a: T, b: T): A -> A; .use(y: Y, z: Z): A -> this.both(y, z) }
"""));}@Test void aTypeAndASubtypeWithDifferentInvariantArgumentsJoinToACommonSupertypeAbove(){ok(List.of("""
A:{} B:{} Top:{} Sup[T]:Top{ .k: T } Z:Sup[B]{ .k -> B }
U:{ .both[T](a: T, b: T): A -> A; .use(y: Sup[A], z: Z): A -> this.both(y, z) }
"""));}
@Test void lambdaParameterCapturedBeforeItsOtherUseIsInferredAsWhenCapturedAfter(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mut A): A -> a.m }
Imm:{ #(a: A): A -> a }
G:{ imm #: A }
Two:{ #[X:*,Y:*](a: X, b: Y): Y -> b }
F1[X:*,R:*]:{ mut #(x: X): R }
Ap:{ #[X:*,R:*](f: mut F1[X,R]): R -> this#f }
U:{ .use: A -> Ap#{x -> Two#(mut G{ # -> Imm#x }, Mut#x)} }
"""));}
@Test void lambdaParameterCapturedAfterItsOtherUseIsInferredFromTheOtherUse(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mut A): A -> a.m }
Imm:{ #(a: A): A -> a }
G:{ imm #: A }
Two:{ #[X:*,Y:*](a: X, b: Y): X -> a }
F1[X:*,R:*]:{ mut #(x: X): R }
Ap:{ #[X:*,R:*](f: mut F1[X,R]): R -> this#f }
U:{ .use: A -> Ap#{x -> Two#(Mut#x, mut G{ # -> Imm#x })} }
"""));}
@Test void lambdaParameterOnlyCapturedInAnImmMethodIsImm(){ok(List.of("""
A:{ mut .m: A -> A }
Imm:{ #(a: A): A -> a }
G:{ imm #: A }
F1[X:*,R:*]:{ mut #(x: X): R }
Ap:{ #[X:*,R:*](f: mut F1[X,R]): R -> this#f }
U:{ .use: mut G -> Ap#{x -> mut G{ # -> Imm#x }} }
"""));}
@Test void lambdaParameterOnlyCapturedInAMutMethodIsMut(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mut A): A -> a.m }
G:{ mut #: A }
F1[X:*,R:*]:{ mut #(x: X): R }
Ap:{ #[X:*,R:*](f: mut F1[X,R]): R -> this#f }
U:{ .use: mut G -> Ap#{x -> mut G{ # -> Mut#x }} }
"""));}
@Test void deepWrittenSupertype(){ok(List.of("A[X:**]:{}\nB:"+"A[".repeat(99)+"B"+"]".repeat(99)+"{}\n"));}
@Test void parameterHashCollidingWithThis(){ok(List.of("""
A:{ .id[Y:**](y:Y):Y -> y; .u(tiJs:A):A -> this.id(tiJs) }
"""));}
@Test void abstractParameterNameNotReusedAsFreshName(){ok(List.of("""
use base.F as F;
A:{ .m(_aimpl:A):A; .k(f:F[A,A]):A; .z:A -> this.k{::.m(this)} }
"""));}
static String box(int n, String in){ return "Box[".repeat(n)+in+"]".repeat(n); }
@Test void supertypeImpliedByAnotherSupertype(){ok(List.of("""
C:{ .m[X](x:X):X; }
B:C{}
A[X]:C,B{}
"""));}
@Test void deepInstantiatedParameter(){ok(List.of("""
N:{}
Box[T:*]:{}
A:{ .mk[T:*]: Box[T] -> Box[T]; .use[S:*](s: Box[S]): N -> N; .go: N -> this.use[imm,D](this.mk[imm,D]) }
""".replace("D", box(98, "N"))));}
@Test void deepInstantiatedParameterNotASubtype(){fail("""
[###]This call to method "Take#(_)" cannot typecheck.
Argument 1 has type "Box[Y]".
That is not a subtype of "Box[[###]
""", List.of("""
N:{}
Box[X]:{}
Take:{ #[Y](c: Box[Y]): N -> N }
Use:{ .m[Y](c: Box[Y]): N -> Take#[D](c) }
""".replace("D", box(98, "N"))));}
@Test void deepCallResult(){fail("""
002| U[X]:{ .m(k: K[[###]]): Box[Box[X]] -> k.get }
   |        [###]^^^^^

While inspecting method call ".get" > ".m(_)" line 2
The body of method ".m(_)" of type declaration "U[_]" is an expression returning "Box[Box[Box[[###]".
Method call "K[_].get" has type "Box[Box[Box[[###]" instead of a subtype of "Box[Box[X]]".

See inferred typing context below for how type "Box[Box[X]]" was introduced: (compression indicated by `-`)
U[X:imm]:{.m(k:K[[###]]):Box[Box[X]]->k.get}
""", List.of("""
A:{} Box[X]:{} K[X]:{ .get: Box[Box[X]] }
U[X]:{ .m(k: K[D]): Box[Box[X]] -> k.get }
""".replace("D", box(97, "A"))));}
@Test void deepArgumentTypeIsNotWritten(){ok(List.of("""
N:{}
Box[X]:{}
U[S]:{ .use(s: Box[Box[S]]): N }
K[X]:{ .get: Box[Box[X]] }
Use:{ .go(u: U[D], k: K[D]): N -> u.use(k.get) }
""".replace("D", box(97, "N"))));}
@Test void deepInferredTypeArgumentFromAnotherArgument(){ok(List.of("""
N:{}
Box[X]:{}
Take:{ #[Y](a: Y, c: Box[Box[Y]]): N -> N }
W[X]:{ .get: Box[Box[X]] }
Use:{ .m(a: D, w: W[D]): N -> Take#(a, w.get) }
""".replace("D", box(97, "N"))));}
@Test void deepImpliedSupertype(){ok(List.of("""
N:{}
Box[X]:{}
C[X]:{}
B[X]:C[Box[X]]{}
A:B[D]{}
""".replace("D", box(97, "N"))));}
@Test void deepVoidDefault(){ok(List.of("""
N:{}
Box[X]:{}
Mk:{ #[T]: D -> {} }
Ign:{ #[K](k: K): N -> N }
Use:{ .m: N -> Ign#(Mk#) }
""".replace("D", box(99, "T"))));}
@Test void deepCallResultIsNotWritten(){ok(List.of("""
N:{}
Box[X]:{ .get: X }
W:{ #[T](t: T): Box[T] -> { .get -> t } }
Use:{ .m(x: D): D -> W#(x).get }
""".replace("D", box(98, "N"))));}
@Test void deepInheritedSupertypeAcrossDeclarations(){ok(List.of("N:{}\nBox[X]:{}\nB0[X]:{}\n"+IntStream.rangeClosed(1, 99).mapToObj(i -> "B"+i+"[X]:B"+(i-1)+"[Box[X]]{}\n").collect(Collectors.joining())));}
@Test void deepInheritedSignature(){ok(List.of("""
N:{}
Box[X]:{}
B[X]:{ .m(x: Box[Box[X]]): N }
A:B[D]{}
""".replace("D", box(97, "N"))));}
@Test void deepInferredHead(){ok(List.of("""
N:{}
Box[X]:{}
K[X]:{ .get: Box[Box[X]] }
Foo[X]:{ .m(x: X): X }
Take:{ #[Z](f: Foo[Z]): N -> N }
Use:{ .go(k: K[D]): N ->
  Take#{ .m(x) -> k.get } }
""".replace("D", box(97, "N"))));}
@Test void deepLiteralMethod(){ok(List.of("""
N:{}
Box[X]:{}
Foo[X]:{ .id: X; .m(x: Box[Box[X]]): N }
Take:{ #[Z](f: Foo[Z]): N -> N }
Use:{ .go(d: D): N ->
  Take#{ .id -> d; .m(x) -> N } }
""".replace("D", box(97, "N"))));}
@Test void deepSupertypeWalkedByTheTypeChecker(){ok(List.of("""
A:{} Top:{} Box[X]:Top{} W[X]:Box[Box[X]]{}
U:{ .m(w: W[D]): Top -> w }
""".replace("D", box(97, "A"))));}
@Test void typeGrowsForever(){failWf("""
006| Use:{ .go: N -> Take#{ .m(x) -> Wrap#(x) } }
   |                      ^^^^^^^^^^^^^^^^^^^^^

While inspecting object literal instance of "Foo[_]"
Type inference finds no type for object literal instance of "Foo[_]".
Each round of inference nests its type one level deeper, as "Foo[Box[Box[...]]]"; it would grow without bound.
""", List.of("""
N:{}
Box[X]:{}
Wrap:{ #[Y](y: Y): Box[Y] -> {} }
Foo[X]:{ .m(x: X): X }
Take:{ #[Z](f: Foo[Z]): N -> N }
Use:{ .go: N -> Take#{ .m(x) -> Wrap#(x) } }
"""));}
@Test void unrelatedTypesInsideAnInferredTypeArgument(){failWf("""
002| U:{ .mk[R]: R; .two[T](a: T, b: T, c: Box[T]): A; .use(y: Y, z: Z): A -> this.two(y, z, this.mk) }
   |                                                                          ^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".two(_,_,_)"
The generic type argument "T" of ".two" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.two[Type1](y, z, this.mk)".
""", List.of("""
A:{} Y:{} Z:{} Box[X]:{}
U:{ .mk[R]: R; .two[T](a: T, b: T, c: Box[T]): A; .use(y: Y, z: Z): A -> this.two(y, z, this.mk) }
"""));}
@Test void unrelatedCandidatesNestedInInferredTypeArgument(){failWf("""
007| User:{ .go(a: A, b: B): A -> Ign#(Mk#.m(a, b)) }
   |                              ^^^^^^^^^^^^^^^^

While inspecting method call "#(_)"
The generic type argument "T" of "#" is inferred from the arguments, but they disagree: some need "Bar[A]", some need "Bar[B]".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "Ign#[Type1](Mk#.m(a, b))".
""", List.of("""
A:{}
B:{}
Bar[X]:{}
Foo[X]:{ .m(a: X, b: X): Bar[X] -> {} }
Mk:{ #[X]: Foo[X] -> {} }
Ign:{ #[T](t: T): A -> A }
User:{ .go(a: A, b: B): A -> Ign#(Mk#.m(a, b)) }
"""));}
@Test void unrelatedTypesInsideAnInferredLiteral(){failWf("""
006| Use:{ .go(y: Y, z: Z): A -> Take#{ Left.choose(y, z) } }
   |                                    ^^^^^^^^^^^^^^^^^

While inspecting method call ".choose(_,_)"
The generic type argument "V" of ".choose" is inferred from the arguments, but they disagree: some need "Y", some need "Z".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "Left.choose[Type1](y, z)".
""", List.of("""
A:{} Y:{} Z:{}
Fork:{ .choose[V](l: V, r: V): V }
Left:Fork{ l,r -> l }
F[R]:{ #: R }
Take:{ #[R](f: F[R]): A -> A }
Use:{ .go(y: Y, z: Z): A -> Take#{ Left.choose(y, z) } }
"""));}
@Test void unrelatedTypesInsideALetValue(){failWf("""
004| Use:{ .go: base.Void -> base.Block#.let x= {Left.choose("Hello", TankNN)}.return{base.Void} }
   |                                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".choose(_,_)"
The generic type argument "Val" of ".choose" is inferred from the arguments, but they disagree: some need "base.Str", some need "TankNN".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in `Left.choose[Type1]("Hello", TankNN)`.
""", List.of("""
Fork:{ .choose[Val](leftVal: Val, rightVal: Val): Val }
Left:Fork{ l,r -> l }
Tank:{} TankNN:Tank{}
Use:{ .go: base.Void -> base.Block#.let x= {Left.choose("Hello", TankNN)}.return{base.Void} }
"""));}
@Test void isoReceiverOverloadFollowsTheExpectedResult(){ok(List.of("""
S:{ read .m: read S -> this; mut .m: mut S -> this }
A:{ .k(s: iso S): mut S -> s.m; .j(s: iso S): read S -> s.m; .i(s: iso S): imm S -> s.m }
"""));}
@Test void receiverLiteralDeclaringTheCalledMethodKeepsItsOwnType(){ok(List.of("""
A: {.m: A}
D: { .k: A -> {.size: A -> D.k}.size }
"""));}
@Test void readNamedLiteralWithoutMutMethodsIsPromotedToIso(){ok(List.of("""
S:{ read .m: read S }
A:{ .k: imm S -> read S{'s .m -> s}; .j: iso S -> imm S{'s .m -> s} }
"""));}
@Test void promotedNamedLiteralKeepsTheWrittenSelfCapability(){ok(List.of("""
S:{ read .m: base.F[S] }
A:{ .k: iso S -> imm S{'s .m -> { s } } }
"""));}
@Test void captureFreeTopLevelThisIsImmInEveryMethod(){ok(List.of("""
A: base.CaptureFree, base.F[A]{ #: A -> this }
B: base.CaptureFree{ read .me: imm A -> A; mut .self: imm B -> this }
"""));}
@Test void captureFreeTopLevelThisInMutMethodInfersTheImmOverload(){ok(List.of("""
A:base.CaptureFree{
  imm .bar: A -> this;
  mut .bar: A -> this;
  mut .foo: A -> this.bar;
  }
"""));}
@Test void captureFreeTopLevelThisInMutMethodWrittenImmOverload(){ok(List.of("""
A:base.CaptureFree{
  imm .bar: A -> this;
  mut .bar: A -> this;
  mut .foo: A -> this.bar[imm];
  }
"""));}
@Test void captureFreeTopLevelThisInMutMethodInfersImmLetType(){ok(List.of("""
A:base.CaptureFree{ mut .foo: A -> base.Block#.let x= {this} .return {x} }
"""));}
@Test void captureFreeTopLevelThisInMutMethodWrittenLetType(){ok(List.of("""
A:base.CaptureFree{ mut .foo: A -> base.Block#.let[A] x= {this} .return {x} }
"""));}
@Test void captureFreeTopLevelThisInImmMethodInfersLetType(){ok(List.of("""
A:base.CaptureFree{ imm .foo: A -> base.Block#.let x= {this} .return {x} }
"""));}
@Test void typingContextShowsSupertypeWrittenByFullName(){fail("""
001| A:base.ToStr{ .str -> base.Void }
   |               --------^^^^^^^^^

While inspecting object literal instance of "base.Void" > ".str" line 1
The body of method ".str" of type declaration "A" is an expression returning "iso base.Void".
Object literal is of type "base.Void" instead of a subtype of "base.Str".

See inferred typing context below for how type "base.Str" was introduced: (compression indicated by `-`)
A:-.ToStr{read .str:-.Str->-.Void}
""", List.of("""
A:base.ToStr{ .str -> base.Void }
"""));}
@Test void typingContextShowsSupertypeWrittenByUseAlias(){fail("""
002| A:Show{ .str -> base.Void }
   |         --------^^^^^^^^^

While inspecting object literal instance of "base.Void" > ".str" line 2
The body of method ".str" of type declaration "A" is an expression returning "iso base.Void".
Object literal is of type "base.Void" instead of a subtype of "base.Str".

See inferred typing context below for how type "base.Str" was introduced: (compression indicated by `-`)
A:Show{read .str:-.Str->-.Void}
""", List.of("""
use base.ToStr as Show;
A:Show{ .str -> base.Void }
"""));}
@Test void useWithASimpleNameIsNotFullyQualified(){failWf("""
001| use Foo as Bar;
   |     ^^^

While inspecting package header
"use" directive refers to "Foo", which is not a full type name.
A "use" directive refers to a type of another package by its full type name, as in "use base.Str as Str;".
""", List.of("""
use Foo as Bar;
Foo:{}
A:{ .m(x: Bar): Foo -> x }
"""));}
@Test void sameCallInReadAndMutMethodsOfOneLiteral(){ok(List.of("""
Foo:{}
Id:{ #[T:*](t: T): T -> t }
K:{ read .a: read Foo; mut .b: read Foo }
User:{ .go(x: mut Foo): mut K -> mut K{ read .a -> Id#(x); mut .b -> Id#(x) } }
"""));}
@Test void deepWrittenOverrideOfAnInheritedSignature(){ok(List.of("""
N:{}
Top:{}
Box[X]:Top{}
B[X]:{ .m(x: Box[Box[X]]): N }
A:B[D]{ .m(x: Top): N -> N }
""".replace("D", box(97, "N"))));}
@Test void typeArgumentWithOpenCapabilityCapturedInANestedLiteral(){ok(List.of("""
Foo:{ .k: Foo -> this }
User:{ .m[X:*](x: imm X, f: base.F[X,Foo]): Foo; .go: Foo -> this.m(Foo, {y -> {#: Foo -> y.k}#}) }
"""));}
@Test void parameterUpdatedWithOpenCapabilityCapturedInANestedLiteral(){ok(List.of("""
A:{}
Foo[X]:{ .m(x: X): A }
Take:{ #[Z](f: Foo[Z]): A -> A }
Id:{ #[Y:*](y: Y, f: base.F[A]): imm Y -> base.Todo! }
Use:{ .go: A -> Take#{ .m(x) -> Id#(x, {# -> x}) } }
"""));}
@Test void capturedLambdaParameterInferredFromIsoArgument(){ok(List.of("""
A:{}
G[T:*]:{ .k(t: T): H }
H:{ .h: A }
Opt[T:*]:{ .match(m: G[T]): H }
Mk:{ #[T:*](t: T): Opt[T] -> base.Nope! }
U:{ .m(a: iso A): H -> Mk#(a).match{ .k(v1) -> { .h -> v1 } } }
"""));}
@Test void isoResultNormalizedToOpenCapabilityCapturedInANestedLiteral(){fail("""
002| U:{ .m: iso A -> base.Block#.let v1 = {A} .return {v1} }
   |     -------------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting method call ".let(_,_)" > ".m" line 2
The body of method ".m" of type declaration "U" is an expression returning "A".
Method call "mut base.Block[_].let(_,_)" has type "A" instead of a subtype of "iso A".

See inferred typing context below for how type "iso A" was introduced: (compression indicated by `-`)
U:{-.Block#[imm,A].let[mut,A](mut -.Ret-tmt[A]{A},mut -.Con-ion[A,mut -.Block[-],A]{(-,-)->-.return[mut](-)})}
""", List.of("""
A:{}
U:{ .m: iso A -> base.Block#.let v1 = {A} .return {v1} }
"""));}
@Test void deepSignatureOfALiteralWithoutBodies(){ok(List.of("""
N:{}
Box[X]:{}
Foo[X]:{ mut .m(x: Box[Box[X]]): N }
Use:{ .go: Foo[D] -> Foo[D]{} }
""".replace("D", box(97, "N"))));}
@Test void deepSupertypeOfAnInferredLiteralWithoutBodies(){ok(List.of("""
N:{}
Box[X]:{}
C[X]:{}
Foo[X]:C[Box[Box[X]]]{}
Take:{ #(f: Foo[D]): N -> N }
Use:{ .go: N -> Take#{} }
""".replace("D", box(97, "N"))));}
@Test void callChainDeeperThanAThousand(){ok(List.of("""
N:{}
Box[X]:{ .wrap: Box[Box[X]] -> {} }
Ign:{ #[K](k: K): N -> N }
Use:{ .go(b: Box[N]): N -> Ign#(bW) }
""".replace("W", ".wrap".repeat(1000))));}
@Test void pickJoinsMutAndReadOfOneTypeParameter(){ok(List.of("""
Pick:{ #[T:*](a:T, b:T):T -> a }
B[X:*]:{ .m(x:mut X, y:read X):read X -> Pick#(x,y) }
"""));}
@Test void pickOfATypeParameterAndVoid(){fail("""
002| C[X:*]:{ .m(x:X, y:base.Void):X -> Pick#(x,y) }
   |          --------------------------~~~~^^~~~~

While inspecting ".m(_,_)" line 2
This call to method "Pick#(_,_)" cannot typecheck.
Argument 2 has type "base.Void".
That is not a subtype of "X" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-#[imm,X](-,y)
""", List.of("""
Pick:{ #[T:*](a:T, b:T):T -> a }
C[X:*]:{ .m(x:X, y:base.Void):X -> Pick#(x,y) }
"""));}
@Test void pickOfThreeUnrelatedTypes(){fail("""
005| U:{ .m:A -> Pick3#(A,B,C) }
   |     --------~~~~~^^~~~~~~

While inspecting ".m" line 5
This call to method "Pick3#(_,_,_)" cannot typecheck.
Argument 2 has type "iso B".
That is not a subtype of "A" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-#[imm,A](-,B,-)
""", List.of("""
Pick3:{ #[T:*](a:T, b:T, c:T):T -> a }
A:{}
B:{}
C:{}
U:{ .m:A -> Pick3#(A,B,C) }
"""));}
@Test void readImmArgumentForAReadParameter(){ok(List.of("""
F2:{ #[T:*](x:read T):base.Void -> base.Void }
D[Y:*]:{ .m(y: read/imm Y): base.Void -> F2#(y) }
"""));}
@Test void literalForATypeParameterArgument(){failWf("""
002| H[X:*]:{ .m: X -> G#[X]({}) }
   |                         ^^

While inspecting object literal "{...}"
Object literal "{...}" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.
""", List.of("""
G:{ #[T:*](x:T):T -> x }
H[X:*]:{ .m: X -> G#[X]({}) }
"""));}
@Test void literalArgumentForAReadImmParameter(){ok(List.of("""
F3:{ #[T:*](x: read/imm T):base.Void -> base.Void }
A:{}
U:{ .m:base.Void -> F3#(A{}) }
"""));}
@Test void baseIdReturningThis(){fail("""
001| I: base.BaseId[I,I]{ #(x)->this }
   |                            ^^^^

While inspecting the file
Type declaration "I" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Compressed relevant code with inferred types: (compression indicated by `-`)
this
""", List.of("""
I: base.BaseId[I,I]{ #(x)->this }
"""));}
@Test void baseIdCallingItself(){fail("""
001| I: base.BaseId[I,I]{ #(x)->this#(x) }
   |                            ^^^^^^^^

While inspecting the file
Type declaration "I" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Compressed relevant code with inferred types: (compression indicated by `-`)
this#(x)
""", List.of("""
I: base.BaseId[I,I]{ #(x)->this#(x) }
"""));}
@Test void pickJoinsIsoAndMutOfOneTypeParameter(){ok(List.of("""
Pick:{ #[T:*](a:T, b:T):T -> a }
B[X:*]:{ .m(x:iso X, y:mut X):mut X -> Pick#(x,y) }
"""));}
@Test void pickJoinsMutAndIsoOfOneTypeParameter(){ok(List.of("""
Pick:{ #[T:*](a:T, b:T):T -> a }
B[X:*]:{ .m(x:mut X, y:iso X):mut X -> Pick#(x,y) }
"""));}
@Test void returnOneTypeParameterAsAnother(){fail("""
001| A:{ .m[X:*,Y:*](x:mut X):mut Y -> x }
   |     ------------------------------^

While inspecting parameter "x" > ".m(_)" line 1
The body of method ".m(_)" of type declaration "A" is an expression returning "mut X".
Parameter "x" has type "mut X" instead of a subtype of "mut Y".

See inferred typing context below for how type "mut Y" was introduced: (compression indicated by `-`)
A:{.m[X:*,Y:*](x:mut X):mut Y->x}
""", List.of("""
A:{ .m[X:*,Y:*](x:mut X):mut Y -> x }
"""));}
@Test void literalMethodParameterUnrelatedToTheTypeArgument(){fail("""
004| U:{ .m:Box[A] -> Box[A]{ .get(x:B):B -> x } }
   |     -------------~~~~~~~~^^^^^^^^^^^^^^^^--

While inspecting object literal instance of "iso Box[A]" > ".m" line 4
Invalid method signature overriding for "Box[A].get(_)".
The method ".get(_)" accepts parameter 1 of type "B".
But "Box[_].get(_)" requires "A", which is not a subtype of "B".
The two types are unrelated.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso Box[A]{.get(x:B):B->x}
""", List.of("""
A:{}
B:{}
Box[T:*]:{ .get(x:T):T }
U:{ .m:Box[A] -> Box[A]{ .get(x:B):B -> x } }
"""));}
@Test void baseIdInheritingHashFromANonBaseIdType(){failWf("""
001| I: base.BaseId[I,I], Impl{}
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^

While inspecting type declaration "I"
Type declaration "I" implements "base.BaseId[_,_]".
It inherits the implementation of "#(_)" from "Impl", which does not implement "base.BaseId[_,_]".
Method "#(_)" must be implemented here, or inherited from a type implementing "base.BaseId[_,_]".
""", List.of("""
I: base.BaseId[I,I], Impl{}
Impl:{ #(x:I):I -> x }
"""));}
@Test void baseIdAsOnANonContainer(){fail("""
002| I: base.BaseId[Box,Box]{ #(x)->x.as{ #(y)->y } }
   |                                ^^^^^^^^^^^^^^^

While inspecting the file
Type declaration "I" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.as(-.BaseId[Box,Box]{#(y:Box):Box->y})
""", List.of("""
Box:{ .as(f: base.BaseId[Box,Box]):Box -> this }
I: base.BaseId[Box,Box]{ #(x)->x.as{ #(y)->y } }
"""));}
@Test void mutMethodInheritedPastAReadOverride(){ok(List.of("""
A:{ read .foo: base.Void -> base.Void; mut .foo: base.Void -> base.Void }
B:A{ read .foo: base.Void -> base.Void }
D:{ mut .foo: base.Void }
C:B,D{}
"""));}
@Test void lambdaMethodTypedByALaterMethod(){ok(List.of("""
Ig:{ #[Y:*](y: Y): base.Void -> base.Void }
Two[X:*]:{ .a(x: X): base.Void; .b: X }
F:{ #[X:*](t: Two[X]): X -> t.b }
U:{ .m: base.Void -> Ig#(F#({ .a(x) -> base.Void; .b -> base.Void })) }
"""));}
@Test void lambdaMethodReturningThroughThisBeforeItsTypeIsKnown(){fail("""
004| U:{ .m: base.Void -> Ig#(F#({ .a -> this.b; .b -> base.Void })) }
   |                               ------~~~~^^^

While inspecting ".a" line 4 > ".m" line 4
This call to method ".b" cannot typecheck.
Method ".b" is not declared on type "U".
Hint:
The method parameter "this" here has type "U".

The method ".b" is defined in the object literal instance of "Two[base.Void]".
No parameter refers to instances of this literal.
To declare one, use the single quote as in the example below:
  Rectangles: { #(width: Nat, height: Nat): Rectangle -> Rectangle:{'rect
    .area: Nat -> width * height;
    .str: Str -> "area: "+(rect.area.str);
    .withWidth(width': Nat): Rectangle -> this#(width', height);
  }}

Available methods on type "U":
-       .m:base.Void

Compressed relevant code with inferred types: (compression indicated by `-`)
this.b
""", List.of("""
Ig:{ #[Y:*](y: Y): base.Void -> base.Void }
Two[X:*]:{ .a: X; .b: X }
F:{ #[X:*](t: Two[X]): X -> t.b }
U:{ .m: base.Void -> Ig#(F#({ .a -> this.b; .b -> base.Void })) }
"""));}
@Test void literalReceiverWithAnUntypedParameter(){failWf("""
002| U:{ .m: A -> { .foo(x): A -> x }.foo(A) }
   |              --^^^^^^^^^^^^^^^--

While inspecting object literal instance of "A"
Cannot infer signature of method ".foo(_)".
No supertype has a method named ".foo(_)" with 1 parameter.
""", List.of("""
A:{}
U:{ .m: A -> { .foo(x): A -> x }.foo(A) }
"""));}
@Test void literalReceiverWithATypedParameter(){ok(List.of("""
A:{}
U:{ .m: A -> { .foo(x: A): A -> x }.foo(A) }
"""));}
@Test void baseIdCallingItselfOnItsArgument(){fail("""
001| I: base.BaseId[I,I]{ #(x)->x#(x) }
   |                            ^^^^^

While inspecting the file
Type declaration "I" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Compressed relevant code with inferred types: (compression indicated by `-`)
x#(x)
""", List.of("""
I: base.BaseId[I,I]{ #(x)->x#(x) }
"""));}
@Test void baseIdAsOnATypeParameterArgument(){fail("""
001| I[X:*]: base.BaseId[X,I[X]]{ #(x)->x.as[I[X]](this) }
   |                                    ^^^^^^^^^^^^^^^^

While inspecting the file
Type declaration "I[_]" implements "base.BaseId[_,_]".
The body of "#(_)" must be "x" or "x.as{...}".
Only those two shapes are the identity function.

Compressed relevant code with inferred types: (compression indicated by `-`)
x.as[imm,I[X]](this)
""", List.of("""
I[X:*]: base.BaseId[X,I[X]]{ #(x)->x.as[I[X]](this) }
"""));}
@Test void readImmResultOfAMutTypeArgument(){ok(List.of("""
Ig:{ #[Y:*](y: Y): base.Void -> base.Void }
A:{}
F:{ #[X:*](a: mut X): read/imm X -> base.Todo! }
U:{ .m(x: mut A): base.Void -> Ig#(F#(x)) }
"""));}
@Test void subtypeArgumentWithAnUninferredTypeArgument(){ok(List.of("""
Ig:{ #[Y:*](y: Y): base.Void -> base.Void }
Box[X:*]:{ .get: X }
SubBox[X:*]:Box[X]{}
Mk:{ #[Y:*]: SubBox[Y] -> base.Todo! }
F:{ #[X:*](b: Box[X], x: X): X -> x }
U:{ .m: base.Void -> Ig#(F#(Mk#, base.Void)) }
"""));}
@Test void literalWithAMethodForAnExplicitTypeParameterArgument(){fail("""
003| H[X:*]:{ .m: X -> G#[X](A{ .k -> base.Void }) }
   |          ---------------^^-------------------

While inspecting object literal instance of "iso A" > ".m" line 3
Object literal instance of "iso A" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso A{.k:-.Void->-.Void}
""", List.of("""
G:{ #[T:*](x: T): T -> x }
A:{ .k: base.Void }
H[X:*]:{ .m: X -> G#[X](A{ .k -> base.Void }) }
"""));}
@Test void literalForAnExplicitTypeParameterArgument(){fail("""
003| H[X:*]:{ .m: X -> G#[X](A{}) }
   |          ---------------^^--

While inspecting object literal instance of "A" > ".m" line 3
Object literal instance of "A" cannot implement "X".
"X" is a generic type parameter; object literals can only implement nominal types.

Compressed relevant code with inferred types: (compression indicated by `-`)
A
""", List.of("""
G:{ #[T:*](x: T): T -> x }
A:{}
H[X:*]:{ .m: X -> G#[X](A{}) }
"""));}
@Test void literalReceiverExpectedAsTheEnclosingLiteralType(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> G#(s, { .j: A -> s }.j) } }
"""));}
@Test void literalImplementingTheEnclosingLiteralType(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> G#(s, { .k -> s; .v -> base.Void }) } }
"""));}
@Test void anonymousLiteralImplementingTheEnclosingAnonymousLiteralType(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> {'s .k -> s; .v -> G#(s, { .k -> s; .v -> base.Void }) } }
"""));}
@Test void literalExpectedAsTheTypeOfTheSelfName(){fail("""
003| U:{ .m: A -> A{'s .k -> s; .v -> G#(s, {}) } }
   |     -----------------------~~~~~~~~~~~~^^~--

While inspecting object literal instance of "iso A" > ".v" line 3 > ".m" line 3
This object literal is missing a required method.
Missing: "imm .k".
Required by: "A".
Hint: add an implementation for ".k" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso A
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> G#(s, {}) } }
"""));}
@Test void literalExpectedAsTheTypeOfTheSelfNameWithAnIndirectSupertype(){fail("""
004| U:{ .m: A -> A{'s .k -> s; .v -> G#(s, {}) } }
   |     -----------------------~~~~~~~~~~~~^^~--

While inspecting object literal instance of "iso A" > ".v" line 4 > ".m" line 4
This object literal is missing a required method.
Missing: "imm .k".
Required by: "A".
Hint: add an implementation for ".k" inside the object literal.

Compressed relevant code with inferred types: (compression indicated by `-`)
iso A
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A0:{}
A:A0{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> G#(s, {}) } }
"""));}
@Test void literalExpectedAsTheTypeOfAnAnonymousSelfName(){failWf("""
002| U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, {}) }.j }
   |                                                 ^^

While inspecting object literal "{...}" (line 2)
The inference concluded that the object literal at line 2, column 49 should extend the object literal at line 2, column 22;
but an object literal can only extend a standalone type.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, {}) }.j }
"""));}
@Test void literalWithAMethodExpectedAsTheTypeOfAnAnonymousSelfName(){failWf("""
002| U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, { .j -> base.Void }) }.j }
   |                                                 ^^^^^^^^^^^^^^^^^^^

While inspecting object literal "{...}" (line 2)
The inference concluded that the object literal at line 2, column 49 should extend the object literal at line 2, column 22;
but an object literal can only extend a standalone type.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, { .j -> base.Void }) }.j }
"""));}
@Test void anonymousSelfNameAsBothArguments(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, s) }.j }
"""));}
@Test void literalExpectedAsATypeDeclaredInAMethod(){fail("""
003| U:{ .m: A -> Foo:A{'s .k -> s; .v -> G#(s, {}) } }
   |     ---------------------------~~~~~~~~~~~~^^~--

While inspecting object literal instance of "Foo" > ".v" line 3 > ".m" line 3
The type "Foo" is not standalone: it is declared inside a method body.
Only a standalone type can be extended or mentioned by name.
A type is standalone if it is declared at top level, or if it implements "base.CaptureFree".

Compressed relevant code with inferred types: (compression indicated by `-`)
Foo
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> Foo:A{'s .k -> s; .v -> G#(s, {}) } }
"""));}
@Test void literalExpectedAsACaptureFreeTypeDeclaredInAMethod(){ok(List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> Foo:A,base.CaptureFree{'s .k -> s; .v -> G#(s, {}) } }
"""));}
@Test void typeArgumentFromAnAnonymousSelfNameAndAnotherType(){failWf("""
003| U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, B) }.j }
   |                                           ^^^^^^^^

While inspecting method call "#(_,_)"
The generic type argument "X" of "#" is inferred from the arguments, but they disagree: some need the anonymous type of the object literal at line 3, column 22, some need "B".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "G#[Type1](s, B)".
""", List.of("""
G:{ #[X:*](a: X, b: X): base.Void -> base.Void }
B:{}
U:{ .m: base.Void -> {'s .j: base.Void -> G#(s, B) }.j }
"""));}
@Test void literalReturningTheSelfNameBeforeAnArgument(){ok(List.of("""
Box[E:*]:{ .get: E }
H:{ #[X:*](b: Box[X], x: X): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> H#({ .get -> s }, s.k) } }
"""));}
@Test void literalReturningTheSelfNameAfterAnArgument(){ok(List.of("""
Box[E:*]:{ .get: E }
H:{ #[X:*](x: X, b: Box[X]): base.Void -> base.Void }
A:{ .k: A; .v: base.Void }
U:{ .m: A -> A{'s .k -> s; .v -> H#(s.k, { .get -> s }) } }
"""));}
@Test void literalReturningAnAnonymousSelfName(){fail("""
004| U:{ .m: base.Void -> {'s .j: base.Void -> H#({ .get -> s }, B) }.j }
   |                          -----------------~^^~~~~~~~~~~~~~~~~~

While inspecting ".j" line 4 > ".m" line 4
This call to method "H#(_,_)" cannot typecheck.
Argument 2 has type "iso B".
That is not a subtype of the anonymous type of the object literal at line 4, column 22 (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-#[imm,_BU](-,B)
""", List.of("""
Box[E:*]:{ .get: E }
H:{ #[X:*](b: Box[X], x: X): base.Void -> base.Void }
B:{}
U:{ .m: base.Void -> {'s .j: base.Void -> H#({ .get -> s }, B) }.j }
"""));}
@Test void methodTArgsArityError_emptyBrackets(){fail("""
003| User:{ read .m(i:Id,a:mut A):mut A-> i.id[](a); }
   |        ------------------------------~^^^^~~~~

While inspecting ".m(_,_)" line 3
This call to method "read Id.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
This method expects 1 generic type argument: "X"; but this call provides no generic type arguments.

Compressed relevant code with inferred types: (compression indicated by `-`)
i.id[read](a)
""", List.of("""
A:{}
Id:{ read .id[X:imm,mut,read](x:X):X->x; }
User:{ read .m(i:Id,a:mut A):mut A-> i.id[](a); }
"""));}
@Test void methodTArgsArityError_capabilityOnlyBrackets(){fail("""
004| User:{ .go(x: Foo): mut K -> { read .a -> Id#[imm](x); .b -> Id#[imm](x) } }
   |                                -----------~~^^~~~~~~~

While inspecting ".a" line 4 > ".go(_)" line 4
This call to method "Id#(_)" cannot typecheck.
Wrong number of generic type arguments for "#(_)".
This method expects 1 generic type argument: "T"; but this call provides no generic type arguments.

Compressed relevant code with inferred types: (compression indicated by `-`)
Id#(x)
""", List.of("""
Foo:{}
Id:{ #[T:*](t: T): T -> t }
K:{ read .a: Foo; mut .b: read Foo }
User:{ .go(x: Foo): mut K -> { read .a -> Id#[imm](x); .b -> Id#[imm](x) } }
"""));}
@Test void methodTArgsArityError_onlyACapability(){fail("""
003| User:{ read .m(i:Id,a:mut A):mut A-> i.id[read](a); }
   |        ------------------------------~^^^^~~~~~~~~

While inspecting ".m(_,_)" line 3
This call to method "read Id.id(_)" cannot typecheck.
Wrong number of generic type arguments for ".id(_)".
This method expects 1 generic type argument: "X"; but this call provides no generic type arguments.

Compressed relevant code with inferred types: (compression indicated by `-`)
i.id[read](a)
""", List.of("""
A:{}
Id:{ read .id[X:imm,mut,read](x:X):X->x; }
User:{ read .m(i:Id,a:mut A):mut A-> i.id[read](a); }
"""));}
@Test void methodTArgsInferredWithoutBrackets(){ok(List.of("""
A:{}
Id:{ read .id[X:imm,mut,read](x:X):X->x; }
User:{ read .m(i:Id,a:mut A):mut A-> i.id(a); }
"""));}
@Test void matchResultInferredFromAllTheCases(){ok(List.of("""
use base.MF as MF;
Blocks: { #[R:*]: mut Block[R] -> {} }
Block[R:*]: {
  mut .return(a: mut MF[R]): R -> a#;
  mut .let[X:*](x: mut MF[X], cont: mut Continuation[X,R]): R -> cont#(x#, this);
  }
Continuation[T:*,R:*]: { mut #(x: T, self: mut Block[R]): R }
North: Direction {::.north}
East : Direction {::.east}
South: Direction {::.south}
West : Direction {::.west}
DirectionMatch[R:**]: { mut .north: R; mut .east: R; mut .south: R; mut .west: R; }
Direction: {
  read .match[R: **](m: mut DirectionMatch[R]): R;
  .turn2: Direction -> Blocks#
    .let d= {this.match{ .north -> East; .east -> South; .south -> West; .west -> North; }}
    .return{d};
  }
"""));}
@Test void declaredReceiverLiteralKeepsItsCapability(){ok(List.of("""
A:{ .k: A -> mut Foo:{ mut .bar: A -> A }.bar }
"""));}
@Test void declaredReceiverLiteralCapturesAMutParameter(){ok(List.of("""
Bar:{ mut .b: base.Void }
A:{ .k(x: mut Bar): base.Void -> mut Foo:{ mut .z: base.Void -> x.b }.z }
"""));}
@Test void declaredReceiverLiteralSelfNameIsNotImm(){fail("""
002| A:{ .k: base.Void -> read Foo:{'s read .z: base.Void -> Use#s }.z }
   |                                   ----------------------~~~^^

While inspecting ".z" line 2 > ".k" line 2
This call to method "Use#(_)" cannot typecheck.
Argument 1 has type "read Foo".
Parameter "s" has type "read Foo" instead of a subtype of "imm Foo".

Type required by each promotion:
- "imm Foo"  (As declared, Strengthen result)

See inferred typing context below for how type "imm Foo" was introduced: (compression indicated by `-`)
A:{.k:-.Void->read Foo:{'s read .z:-.Void->Use#(s)}.z[read]}
""", List.of("""
Use:{ #(f: Foo): base.Void -> base.Void }
A:{ .k: base.Void -> read Foo:{'s read .z: base.Void -> Use#s }.z }
"""));}
@Test void joinOfTypesImplementingAGenericHeadTwice(){ok(List.of("""
Box[T]:{}
C:Box[A],Box[C]{}
D:Box[A]{}
A:{ .m[X](x: X, y: X): X -> y; .k: Box[A] -> this.m(C, D) }
"""));}
@Test void joinOfTypesImplementingAGenericHeadTwiceIsAmbiguous(){failWf("""
004| A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(C, D)) }
   |                                                                          ^^^^^^^^^^^^

While inspecting method call ".m(_,_)"
The generic type argument "X" of ".m" is inferred from the arguments, but they disagree: some need "C", some need "D".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.m[Type1](C, D)".
""", List.of("""
Box[T]:{}
C:Box[A],Box[C]{}
D:Box[A]{}
A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(C, D)) }
"""));}
@Test void joinOfTypesImplementingAGenericHeadTwiceInTheOtherOrderIsAmbiguous(){failWf("""
004| A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(C, D)) }
   |                                                                          ^^^^^^^^^^^^

While inspecting method call ".m(_,_)"
The generic type argument "X" of ".m" is inferred from the arguments, but they disagree: some need "C", some need "D".
No type is a supertype of all of them.
Write the generic type argument explicitly, as in "this.m[Type1](C, D)".
""", List.of("""
Box[T]:{}
C:Box[C],Box[A]{}
D:Box[A]{}
A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(C, D)) }
"""));}
@Test void argumentImplementingAGenericHeadTwiceIsAmbiguous(){fail("""
003| A:{ .m[X](b: Box[X]): A -> this; .k: A -> this.m(C) }
   |                                  ---------~~~~^^^~~

While inspecting ".k" line 3
This call to method "A.m(_)" cannot typecheck.
Argument 1 has type "iso C".
That is not a subtype of "Box[base.Void]" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-.m[imm,-.Void](C)
""", List.of("""
Box[T]:{}
C:Box[A],Box[C]{}
A:{ .m[X](b: Box[X]): A -> this; .k: A -> this.m(C) }
"""));}
@Test void argumentImplementingAGenericHeadTwiceInTheOtherOrderIsAmbiguous(){fail("""
003| A:{ .m[X](b: Box[X]): A -> this; .k: A -> this.m(C) }
   |                                  ---------~~~~^^^~~

While inspecting ".k" line 3
This call to method "A.m(_)" cannot typecheck.
Argument 1 has type "iso C".
That is not a subtype of "Box[base.Void]" (the type required by the method signature).

Compressed relevant code with inferred types: (compression indicated by `-`)
-.m[imm,-.Void](C)
""", List.of("""
Box[T]:{}
C:Box[C],Box[A]{}
A:{ .m[X](b: Box[X]): A -> this; .k: A -> this.m(C) }
"""));}
@Test void joinOfASubtypeRefiningAGenericHeadOfItsSupertype(){ok(List.of("""
Box[T]:{}
R:Box[R]{}
S:R,Box[S]{}
A:{ .m[X](x: X, y: X): X -> y; .ig[Y](y: Y): A -> this; .k: A -> this.ig(this.m(R, S)) }
"""));}
@Test void nestedLiteralCapturesALateInferredParameter(){ok(List.of("""
use base.F as F;
Foo:{ .foo: A }
A:{
  .app[T](t: T, f: F[T,A]): A -> f#t;
  .ig(z: Foo): A -> z.foo;
  .ig2[W](w: W): A -> A;
  .k[X](x: X): A -> this.app(x, {y -> this.ig({ .foo -> this.ig2(y) })});
  }
"""));}
@Test void nestedLiteralWithAGenericCapturesALateInferredParameter(){ok(List.of("""
use base.F as F;
Foo:{ .foo: A }
A:{
  .app[T](t: T, f: F[T,A]): A -> f#t;
  .ig(z: Foo): A -> z.foo;
  .ig2[W](w: W): A -> A;
  .ig3(a: A): A -> a;
  .k[X,Y](x: X, v: Y): A -> this.app(x, {y -> this.ig({ .foo -> this.ig2(v).ig3(this.ig2(y)) })});
  }
"""));}
@Test void emptyLiteralArgumentDoesNotDecideATypeArgument(){ok(List.of("""
Sup:{}
Sub:Sup{}
Box[X,Y]:{}
K:{ #[X,Y](a: X, b: Box[X,Y], c: Y): X -> a }
M:{ .m(y: Sub, z: Sup): Sup -> K#(y, {}, z) }
"""));}
@Test void emptyLiteralArgumentFollowsATypeArgumentBelowTheResultType(){ok(List.of("""
Sup:{}
Sub:Sup{}
Box[X]:{}
K:{ #[X](a: X, b: Box[X]): X -> a }
M:{ .m(y: Sub): Sup -> K#(y, {}) }
"""));}
@Test void innerLiteralCapturesALateInferredParameter(){ok(List.of("""
use base.F as F;
Foo:{ .foo: A }
Ret[R]:{ #: R }
A:{
  .app[T](t: T, f: F[T,A]): A -> f#t;
  .ig(z: Foo): A -> z.foo;
  .ig4[W](r: Ret[W]): A -> A;
  .k[X](x: X): A -> this.app(x, {y -> this.ig({ .foo -> this.ig4({y}) })});
  }
"""));}
@Test void typeExpressionDoesNotShiftFreshGenericNames(){ok(List.of("""
S:{ .s[K](k: K): K -> k; }
D[K]:S{}
T[K]:D[K]{ .m: S -> S.s[S]{.s k -> k}; }
"""));}
@Test void selfNameCallWithAnExpectedTypeGetsItsCapability(){ok(List.of("""
A:{ mut .a: mut A }
B:{ #: mut A -> mut A{'s .a -> s.a} }
"""));}
@Test void letOfAGenericParameterUsedInTheReturn(){ok(List.of("""
A:{ .k[X](x: X): base.Void -> base.Block#.let y= {x} .return{ base.Block#(y, base.Void) } }
"""));}
@Test void selfNameCallOnAnImmLiteralGetsItsCapability(){ok(List.of("""
A:{}
Foo:{ .foo: A; read .r: A }
B:{ .k: A -> B.ig(Foo{'s .foo -> s.r; read .r -> A }); .ig(z: Foo): A -> z.foo }
"""));}
@Test void declaredReceiverLiteralCapturesThisInAReadMethod(){ok(List.of("""
A:{ read .q: A; read .k: A -> read Foo:{ read .z: A -> this.q }.z }
"""));}
@Test void emptyLiteralWithAnExpectedTypeWidenedToASupertype(){ok(List.of("""
C:base.WidenTo[C]{}
B:C{}
A:{ .m: B -> {} }
"""));}
@Test void emptyLiteralArgumentWithAnExpectedNumberLiteralType(){ok(List.of("""
A:{ .m(x: 45): A -> A; .k: A -> this.m({}) }
"""));}
@Test void typeNameExpressionWidenedToASupertypeWithALessSpecificMethod(){ok(List.of("""
C:{ .k: C }
B:C,base.WidenTo[C]{ .k: B -> this }
A:{ .m: C -> B }
"""));}
@Test void typeNameExpressionWidenedPastAnIntermediateOverride(){ok(List.of("""
C:{ .k: C -> this }
D:C{ .k: D -> this }
B:D,base.WidenTo[C]{}
A:{ .m: C -> B }
"""));}
@Test void typeNameExpressionWidenedToAnUnrelatedTypeWithAnotherGenericArity(){ok(List.of("""
C:{ .k[Y](y: Y): Y -> y }
B:base.WidenTo[C]{ .k(x: C): B -> this }
A:{ .m: B -> B }
"""));}
@Test void emptyLiteralWithAnExpectedTypeWidenedToAnUnrelatedAbstractType(){ok(List.of("""
C:{ .k: C }
B:base.WidenTo[C]{}
A:{ .m: B -> {} }
"""));}
@Test void emptyLiteralRefinedFromAReadExpectedTypeToAnImmExpectedType(){ok(List.of("""
P:{}
Box[X:**]:{ .get: X }
Ids:{ #[X:**](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[P]): read P -> Ids#({}, b) }
"""));}
@Test void emptyLiteralRefinedFromAnIsoExpectedTypeToAMutExpectedType(){ok(List.of("""
P:{}
Box[X:**]:{ .get: X }
Ids:{ #[X:**](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[mut P]): iso P -> Ids#({}, b) }
"""));}
@Test void emptyLiteralWithAMutAbstractMethodRefinedToAnImmExpectedType(){ok(List.of("""
P:{ mut .k: P }
Box[X:**]:{ .get: X }
Ids:{ #[X:**](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[P]): read P -> Ids#({}, b) }
"""));}
@Test void emptyLiteralRefinedFromAnAbstractSupertypeToAConcreteSubtype(){ok(List.of("""
P:{}
Sup:{ .name: P }
Con:Sup{ .name -> P }
Box[X]:{ .get: X }
Ids:{ #[X](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[Con]): Sup -> Ids#({}, b) }
"""));}
@Test void emptyLiteralRefinedFromASupertypeToASubtypeWithOneMoreMethod(){ok(List.of("""
Sup:{}
Sub:Sup{ .k: Sub -> this }
Box[X]:{ .get: X }
Ids:{ #[X](a: X, b: Box[X]): X -> a }
User:{ .m(b: Box[Sub]): Sup -> Ids#({}, b) }
"""));}
@Test void typeExpressionOfATypeWithAnOperatorMethodContainingAnArrow(){ok(List.of("""
Q:{ -->(a: Q): Q -> a }
A:{ .k: Q -> Q }
"""));}
@Test void typeExpressionOfATypeWithAClosedCurlyStringLiteralTypeInAMethod(){ok(List.of("""
Q:{ .m: "}" -> "}" }
A:{ .k: Q -> Q }
"""));}
@Test void lambdaParameterCapturedInAMutLiteralAndUsedAsMutHIsMut(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mutH A): A -> a.m }
G:{ mut #: A }
F1[X:*,R:*]:{ #(x: X): R }
Ap:{ #[X:*,R:*](f: F1[X,R]): R -> this#f }
User:{ .use: mut G -> Ap#{x -> mut G{ Mut#x }} }
"""));}
@Test void lambdaParameterCapturedInAMutLiteralAndUsedAsMutHIsMutAlsoWhenTheBoundAllowsMutH(){ok(List.of("""
A:{ mut .m: A -> A }
Mut:{ #(a: mutH A): A -> a.m }
G:{ mut #: A }
F1[X:**,R:*]:{ #(x: X): R }
Ap:{ #[X:**,R:*](f: F1[X,R]): R -> this#f }
User:{ .use: mut G -> Ap#{x -> mut G{ Mut#x }} }
"""));}
@Test void lambdaParameterCapturedInAReadLiteralAndUsedAsReadHIsRead(){ok(List.of("""
A:{ read .m: A -> A }
Use:{ #(a: readH A): A -> a.m }
G:{ read #: A }
F1[X:**,R:**]:{ #(x: X): R }
Ap:{ #[X:**,R:**](f: F1[X,R]): R -> this#f }
User:{ .use: read G -> Ap#{x -> read G{ Use#x }} }
"""));}
}
