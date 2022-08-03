# Assignment 6: Lazy Programming

You may do this assignment in pairs. Each member of the pair is responsible for
participating in all elements of the assignment.

## Quick Links:

- [Part 1](#part-1-modular-reasoning-queuetxt)
- [Part 2](#part-2-lazy-streams-streamsml)
<!-- - [Part 3](#part-3-efficient-functional-queues-queueml) -->
- [Part 3 (OPTIONAL)](#part-3)

## Part 1: Modular Reasoning (`queue.txt`)

In this problem, we will investigate proof techniques that allowing us to reason
about several different implementations of the same abstract type. Specifically,
we want to know: When can you replace one implementation of a signature with
another without breaking any client code?

Informally, the answer is that you can swap implementations when they behave the
same. There is a theorem about pure, polymorphic functional programming
languages called *relational parametricity*, which justifies the following
formalization of this intuition: One implementation of a signature can be
replaced by another without breaking any client code if and only if there exists
a mathematical relation R between the two implementations of the abstract type
that is preserved by all the operations in the signature.

We already saw this idea in play in class. In this assignment, we will explore
the idea of defining the relation R between the two implementations using an
abstraction function.

### Proving Modules Equivalent

When given a signature like this:

```
module type SIG = sig
  type abs
  val v1 : T1
  val v2 : T2
  val v3 : T3
end
```

and two modules like this:

```
module M1 : SIG = struct
  type abs = m1_type
  let v1 = ...
  let v2 = ...
  let v3 = ...
end

module M2 : SIG = struct
  type abs = m2_type
  let v1 = ...
  let v2 = ...
  let v3 = ...
end
```

We would like to be able to prove that `M1` and `M2` are indistinguishable to
clients. If `M2` is very simple and easy to understand (but perhaps inefficient)
one might call `M2` a "specification." If `M1` is more complex, but perhaps more
efficient, then one might call `M1` a module that "implements the specification
efficiently". One might also say that `M2` is "more abstract" than `M1`.

One the way a programmer proves that two modules are equivalent is to proceed as
follows.
1. Define a basic relationship between values of the abstract type `abs`. If one
    module is strictly "more abstract" than the other, a good way to define the
    relation is to use an *abstraction function*. Note that the programmer doing
    the proof of equivalence gets to pick any abstraction function that they
    want to use. An abstraction function converts a value from one module in to
    the equivalent value in the other module. Let's call our abstraction
    function `abstract`, we say *two components named `v` from modules `M1` and
    `M2` are related at type `abs`* iff:

    ```
    abstract (M1.v) == M2.v
    ```

2. Extend that relationship so that it covers other types like pair types,
    option types and function types&mdash;this extension is mechanical and works
    the same way no matter what two modules you are trying to compare. Given a
    basic relation over the type abs defined using an abstraction function as
    above, we define the following additional relations:
    - *Two components named `v` from modules `M1` and `M2` are related at type
        `float`* iff:

        ```
        M1.v == M2.v
        ```

    - *Two components named `v` from modules `M1` and `M2` are related at type
        `char`* iff:

        ```
        M1.v == M2.v
        ```

    - *Two components named `v` from modules `M1` and `M2` are related at type
        `int`* iff:

        ```
        M1.v == M2.v
        ```

        (and so on, for other basic types ..)
    - *Two components named `v` from modules `M1` and `M2` are related at type
        `t1 * t2`* iff their components are related. In other words, if `M1.v ==
        (v1a, v1b)` and `M2.v == (v2a, v2b)` then
        - *`v1a` must be related to `v2a` at type `t1`*, and
        - *`v1b` must be related to `v2b` at type `t2`*
    - *Two components named `v` from modules `M1` and `M2` are related at type
        `t option`* iff:
        - `M1.v == None` and `M2.v == None`, or
        - `M1.v == Some v1` and `M2.v == Some v2`, and *`v1` is related to `v2`
            at type `t`*
    - *Two components named `v` from modules `M1` and `M2` are related at the
        function type `t1 -> t2`* iff given related arguments, the application
        of functions `M1.v` and `M2.v` to those arguments produces related
        results. In other words, for arbitrary inputs `v1`, `v2` *that are
        related at type `t1`*, it must be the case that *the outputs `(M1.v v1)`
        and `(M2.v v2)` are related at type `t2`*

### Equivalent BOOL Modules

Here is how to go about that process when proving the equivalence of two modules
that both implement a very simple boolean signature:

```
module type BOOL = sig
  type b
  val tru : b
  val fal : b
  val not : b -> b
  val and : b * b -> b
end
```

And here are two modules that implement that signature:

```
module M1 : BOOL = struct
  type b = int
  let tru = 1
  let fal = 0
  let not b =
    match b with
      1 -> 0
    | 0 -> 1
  let and bs =
    match bs with
      1,1 -> 1
    | _,_ -> 0
end

module M2 : BOOL = struct
  type b = bool
  let tru = true
  let fal = false
  let not b =
    if b then false else true
  let and bs =
    match bs with
      true,true -> true
    | _,_ -> false
end
```

Now, first we need to define what it means for the two modules to be related at
the abstract type b. In other words, we must define the *abstraction function*
that relates values of the abstract type. Here is the most natural abstraction
function to choose:

```
let abstract b =
  match b with
    0 -> false
  | 1 -> true
```

You can see that that abstraction function converts values with type b from
module `M1` in to values with type b from module `M2`. Hence to compare a basic
value named v with type b from modules `M1` and `M2`, we would compare as
follows:

```
abstract (M1.v) == M2.v
```

<!--
**Definition 1:** `M1.v ~~> M2.v : b` if and only if `abstract (M1.v) == M2.v`

Ok, now that we have the basic relation, we have to prove that each component of
the module is faithful to that relation. In other words we have to prove the
following things
1. `M1.tru ~~> M2.tru : b`
2. `M1.fal ~~> M2.fal : b`
3. `M1.not ~~> M2.not : b -> b`
4. `M1.and ~~> M2.and : b*b -> b`
-->

Because of how we chose to define the basic relation on type b, to show the two
boolean modules `M1` and `M2` are equivalent, we have to prove:

1. `abstract (M1.tru) == M2.tru`
2. `abstract (M1.fal) == M2.fal`
3. Consider any arguments `v1:int`, `v2:bool` such that `abstract (v1) == v2`,
    we must prove that `abstract(M1.not v1) == M2.not v2`.
4. Consider any arguments `(v1,v2):int*int` and `(v3,v4):bool*bool` such that:
    - `abstract v1 == v3`
    - `abstract v2 == v4`

    we must prove that `abstract(M1.and (v1,v2)) == M2.and (v3,v4)`.

Each of those 4 proof requirements above involves some equational reasoning
exactly like the equational reasoning that you have done previously in this
class. Consequently, you should not have much trouble proving the 4 facts above.

### Equivalent QUEUE Modules

Now, your job will be to carry out some similar proofs in a more complicated
setting: Proofs about equivalent `Queue` modules. Below we list a signature for
queues.

```
module type QUEUE = sig
  type q
  val emp : q
  val ins : int * q -> q
  val rem : q -> (int * q) option
end
```

and here are two implementations:

```
module M1 : QUEUE = struct
  type q = int list * int list

  let emp = ([], [])

  let ins (i,q) =
    let (front, back) = q in
    (front, i::back)

  let rem q =
    match q with
      ([],[]) -> None
    | (hd::front, back) -> Some (hd, (front,back))
    | ([], back) ->
       (match List.rev back with
         hd::tail -> Some (hd, (tail, []))
        | _ -> failwith "impossible")
end

module M2 : QUEUE = struct
  type q = int list

  let emp = []

  let ins (i,q) = q @ [i]

  let rem q =
    match q with
      [] -> None
    | hd::tail -> Some (hd, tail)
end
```

**See the file `queue.txt` for questions on proving things about these
implementations. The file `theory.ml` contains the code listed above.**

Note: We removed the `QUEUE` signature ascription from the modules `M1` and `M2`
defined in `theory.ml`. Why did we do that? We did it because we want you to
write a relation that relates the *internal representations* of the two modules.
The signature ascription prevents us from doing that. (Though another choice
would have been to write a function `rep` that exposes the representation to the
outside world.)

## Part 2: Lazy Streams (`streams.ml`)

In class, we looked at a couple of ways to implement infinite streams, which you
can check out in the lecture notes. In the referenced code, we repeatedly used
functions with type `unit ->'a * 'a stream`. Such functions are sometimes called
"suspended computations." They are very much like plain expressions with type
`'a * 'a stream` except that plain expressions are *evaluated right away*
whereas functions are not evaluated until they called. In other words,
evaluation is *delayed*. That delay was critical in our implementation of the
stream infinite data structure. Without the delay, we would have written code
containing infinite loops.

In general, we can implement suspended or delayed computations that return a
value with type `'a` with just a function with type `unit -> 'a`. Let's try it:

```
type 'a delay = unit -> 'a

(* create a delayed computation *)
let create_delay (d:unit -> 'a) = d

(* execute a delayed computation *)
let force_delay (d:'a delay) : 'a = d ()
```

You'll notice, however, that this implementation (like our original stream
implementation) can incur extra, unnecessary work when we force the same delay
more than once. For instance:

```
let adder () =
  let l = [1;2;3;4;5;6;7;8;9;0] in
  List.fold_left (+) 0 l

let x = force_delay adder
let y = force_delay adder
```

Above, we run over the list l once to compute x and then we do exactly the same
thing again to compute y. A smarter implementation would use a technique called
*memoization*, which saves away the result of forcing a delay the first time so
that any subsequent time the computation is forced, it can simply look up the
already-computed result. A delayed computation coupled with memoization is
called a *lazy* computation. Here is how we might implement a general-purpose
library for lazy computations, as seen in lecture, but with some added error-
handling:

```
type 'a thunk = Unevaluated of (unit -> 'a) | Evaluated of 'a | Error of exn
type 'a lazy_t = ('a thunk) ref

let create_lazy (f : unit -> 'a) : 'a lazy_t =
  ref ( Unevaluated f )

let force_lazy (l:'a lazy_t) : 'a =
  match !l with
  | Error exn -> raise exn
  | Evaluated a -> a
  | Unevaluated f ->
        try
	  let result = f () in
	    l := Evaluated result;
          result
        with
        | exn -> l := Error exn;
                 raise exn
```

Note that if the underlying function f that you use to create a lazy computation
has no effects other than raising an exception&mdash;does not print, does not
mutate external data structures, does not read from standard input, etc.&mdash;
then an outside observer cannot tell the difference between a lazy computation
and an ordinary function with type `unit -> 'a` (except that the lazy
computation is faster if you force it a 2nd, 3rd or 4th time). If, on the other
hand, your function f does have some effects (like printing) then you will see a
difference between using a lazy computation and using a function with type `unit
-> 'a`. For instance, this code:

```
let a = create_lazy (fun () -> (1 + (print_string "hello\n"; 1)))

let _ = force_lazy a
let _ = force_lazy a
```

only prints `hello\n` once, not twice.

You'll notice that it is a little bit verbose to have to write things like:

```
let a = create_lazy (fun () -> ...)
```

Consequently, OCaml provides convenient built-in support for creating and using
lazy computations via the `Lazy` module, which is
[documented here](https://caml.inria.fr/pub/docs/manual-ocaml/libref/Lazy.html).
This module is not just an ordinary module&mdash;it is really a language
extension as it changes the way OCaml code is evaluated. In particular, any code
that appears inside the lazy constructor

```
lazy (...)
```

is suspended and is not executed until the lazy computation is forced. It is
just like you wrote

```
create_lazy (fun () -> ...)
```

**See the file `streams.ml` for a series of questions concerning implementing
streams using OCaml's `Lazy` module. You will also need to read the OCaml
documentation on `Lazy` data
[here](https://caml.inria.fr/pub/docs/manual-ocaml/libref/Lazy.html).**

<!--
## Part 3: Efficient Functional Queues (`queue.ml`)

One of the most important uses of lazy data structures is to improve the
performance of various algorithms. Sometimes laziness and memoization can
improve algorithm performance by orders of magnitude. Recall the more efficient
queues (module M1) from Part 1, which were implemented as a pair of lists:

```
type q = int list * int list
```

Now consider the following sequence of operations:

```
let q0 = emp in              (* 0 *)
let q1 = ins (3,q0) in       (* 1 *)
let q2 = ins (5,q1) in       (* 2 *)
let q3 = ins (7,q2) in       (* 3 *)
let q4 = ins (9,q3) in       (* 4 *)
let Some (_,q5) = rem q4 in  (* 5 *)
let Some (_,q6) = rem q5 in  (* 6 *)
let Some (_,q7) = rem q6 in  (* 7 *)
let Some (_,q8) = rem q7 in  (* 8 *)
q5
```

Each of lines 0-4 and line 6-8 are constant time operations. However, line 5
takes time on the order of the length of the constructed queue q4 because it
must reverse the list representing the "back" of the queue. Still, overall, for
any sequence of N operations constructed like the sequence above, on computation
will require on the order of 2\*N list operations. (One can conclude this is
true using amortized analysis.) You probably explored a similar problem in COS
226. However, this result only holds when *each queue is used once*, like in the
sequence above. If a queue is reused, like in the sequence below, one may be
forced to execute up to N^2/2 list operations.

```
let q0 = emp in              (* 0 *)
let q1 = ins (3,q0) in       (* 1 *)
let q2 = ins (5,q1) in       (* 2 *)
let q3 = ins (7,q2) in       (* 3 *)
let q4 = ins (9,q3) in       (* 4 *)
let Some (_,q5) = rem q4 in  (* 5 *)
let Some (_,q5) = rem q4 in  (* 6 *)
let Some (_,q5) = rem q4 in  (* 7 *)
let Some (_,q5) = rem q4 in  (* 8 *)
q5
```

Above lines 5-8 all incur the cost of reversing the list.

One of the benefits of implementing a data structure like a queue in a
functional style is exactly that you can both *create a new data structure* from
the old data structure (eg: a new queue with more or fewer elements) and you can
also *reuse* the old data structure as often as you want. In an imperative
implementation of a queue (like the ones you probably did in 226) you can't
reuse your queue&mdash;once you do an imperative update by inserting or removing
an item, the old queue is gone.

When data structures can be reused (because they never change) they are
typically called *persistent*. It is typically more difficult to implement
efficient persistent data structures than non-persistent ones&mdash;that's
natural because persistence is a useful bonus property. In fact, there is a
whole literature on how to implement persistent data structures efficiently
(see, for example,
[Chris Okasaki's book on purely functional data structures](https://www.amazon.com/Purely-Functional-Structures-Chris-Okasaki/dp/0521663504)).
In this course, we encourage the use of persistent data structures whenever
possible because it is typically much easier to write correct programs when your
data is persistent: all of the data structure invariants that you establish will
persist forever; you do not have to keep track of *when* the invariants are
valid and *when* they become invalid due to a mutation.

In `queue.ml`, we have used the ideas discussed above to implement AmortizedQ, a
variant of the queue interface that is a little slower when a queue is not used
persistently, but can be substantially faster when it is. In fact, no matter
what sequence of queue operations are performed, this last implementation never
incurs more than a linear number of list operations to perform all of them. The
AmortizedQ is somewhat similar to the queue implemented in module M1 as it uses
a pair of lists -- one for the front and one for the back of the queue. However,
the lists are not ordinary lists, they are `lazy lists`. The module LL in
`queue.ml` implements these lazy lists. The representation of an AmortizedQ also
includes a pair of integers. See if you can figure out how AmortizedQ works and
what some of the invariants governing the data structure are. It is really a
pretty cool data structure.

**Your jobs in `queue.ml`:**
- There is one function missing in AmortizedQ, the function rep_inv. The
    intention is that this function could be used to check the *representation
    invariant(s)* of an AmortizedQ. Recall, the representation invariant(s) of a
    data structure are those invariants that are always true of all data
    structures produced by the module. In other words, if client code were to
    execute rep_inv on any value with type 'a AmortizedQ.q, rep_inv should
    evaluate to true. Fill in the body of rep_inv so that it checks as many of
    the representation invariants of an AmortizedQ as you can. (ie: the
    simplest, safe way to fill in rep_inv is to just make it return true all the
    time, but that would not capture many of the interesting invariants of the
    data structure&mdash;make rep_inv as precise as you can).
- There is also a framework for performance testing in `queue.ml`. Use this
    framework to illustrate that AmortizedQs are substantially more efficient
    than the other queue variants in certain circumstances (follow directions in
    the functor Performance).
-->

## Part 3

**This section of the assignment (4.1 - 4.5) is OPTIONAL. Many students find
this problem mind-blowing and fun, but it is OPTIONAL. You don't need to do it
if you don't want to.**

A lazy computation uses memoization to avoid recomputing the result of executing
a single expression. A more general kind of memoization avoids recomputing the
results of a whole class or set of expressions. In this part of the assignment,
we will explore using memoization for functions instead of simple expressions. A
memoized function f never recomputes f x for the same argument x twice.

To build generic support for function memoization, we will use a dictionary to
store a mapping from function inputs to outputs already computed. You can think
of this dictionary like a cache if you want: The cache saves away function
results for later reuse.

To begin, look at the naive implementation of the Fibonacci sequence defined in
the module `Fib` provided in `fib.ml`.

```
(* slow fib! *)
module Fib : FIB =
struct
  let rec fib (n : int) : int =
    if n > 1 then
      fib (n-1) + fib (n-2)
    else
      n
end
```

Anyone who has taken COS 226 will recognize this as a horrendously inefficient
version of the Fibonacci sequence that takes exponential time because we
recompute fib n for small values of n over and over and over again instead of
reusing computation. The most efficient way to compute the Fibonacci numbers in
OCaml is something like this:

```
(* fast fib! *)
module FastFib : FIB =
struct
  let fib (n : int) : int =
    (* f1 is fib(i-1) and f2 is fib (i-2) *)
    let rec aux i f1 f2 =
      if i = n then
      f1 + f2
      else
      aux (i+1) (f1+f2) f1
    in
    if n > 1 then aux 2 1 0
    else n
end
```

Intuitively, what is happening here is that instead of recomputing `fib(n-1)`
and `fib(n-2)` over and over again, we are saving those results and then reusing
them. When computing the fibonacci sequence, one only has to save away the last
two results to compute the next one. In other computations, we must save away a
lot of data, not just two elements. Sometimes we don't know exactly what we need
to save so we might want to save all the data we have space for. There are
entire businesses built around memoization and caching like this.
[Akamai](https://www.akamai.com/) is one that comes to mind&mdash;they cache web
page requests on servers close to customers who make requests in order to make
web response times faster. In any event, the idea of caching is clearly a
fundamental concept in computer science. Hence, we are going to build generic
caching infrastructure for OCaml computations. This generic caching
infrastructure is going to save away *all* results computed by a function. This
is more than we need to save away to compute Fibonnacci *once* (and it is a big
waste of space in this case), but if we wanted to call Fibonacci many times,
there would be savings across the many calls. (True, there aren't many critical
applications that I can think of that make 1,000,000 calls to the Fibonacci
function but it does make a good, simple test case!)

### Question 4.1

Finish the `MemoFib` functor in `fib.ml` by writing a memoized version of
Fibonacci. In this implementation, you will save away *all* results from ever
calling the function `fib`, including all recursive calls that `fib` might make
to itself. You will do this by representing the (input,output) mapping using a
reference containing a persistent dictionary. It is important that the
dictionary be shared between all calls to `MemoFibo`, so that results are reused
between multiple top-level calls (ie: if you call fib 10000 first and then some
time later in your application call fib 10001, the second call should be
instantaneous since you'll reuse all the work you did on the first call).

In this assignment, we will use OCaml's `Map` library to implement dictionaries.
To investigate OCaml's `Map` library, start by looking
[here](https://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.html). You'll note
that from that web page, you can click on links to find definitions of
[`OrderedType`](https://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.OrderedType.html)
signature and the
[`Map.S`](https://caml.inria.fr/pub/docs/manual-ocaml/libref/Map.S.html), which
is the signature of a module implementing a `Map`. The functor `Map.Make` takes
a module with a `Map.OrderedType` as an argument and produces module with type
`Map.S` as a result.

If you don’t know where to start implementing `MemoFib`, one good strategy is to
use a pair of mutually recursive functions: make one function in the pair the
fib function required by the signature; make the other function responsible for
checking and updating the mapping. The benefit to this strategy is that it lets
you separate memoizing from the function being memoized.

### Question 4.2

Instead of hand-rolling a new version of every function that we’d like to
memoize, it would be nice to have a higher-order function that produces a
memoized version of any function. A totally reasonable—but wrong—first attempt
at writing such an automatic memoizer is shown below (and also may be found in
`memoizer.ml`).

```
module PoorMemoizer (D : DICT) : (POORMEMOIZER with type key = D.key) =
struct
  type key = D.key

  let memo (f : key -> 'a) : key -> 'a =
    let f_memoed x =
      let history = ref (D.empty) in
      try D.find x (!history) with
        Not_found ->
	    let result = f x in
	        history := D.add x result (!history);
		    result
    in
    f_memoed
end
```

What is wrong with this code? For example, apply the functor and use it to
memoize an implementation of Fibonacci. You should observe that Fibonacci is
much slower than the hand-rolled version you wrote. (If not, your hand-rolled
version is wrong!) Why?

The goal of this part is to finish off the `Memoizer` functor in `memoizer.ml`
by writing an automatic memoizer that doesn’t have the problems of the
`PoorMemoizer`. Notice that `Memoizer` has a different signature than
`PoorMemoizer`. Functions that can be memoized by `Memoizer` take a new
argument: rather than having type `key -> ’a `, they have type `(key -> ’a) ->
(key -> ’a)`. When implementing `Memoizer`, assume that any function you memoize
uses this new first argument instead of directly calling itself recursively. As
an example, Here is the factorial function crafted in this style:

```
let fact_body (recurse:int->int) (n:int) : int =
  if n <= 0 then 1
  else n * (recurse (n-1))


let rec fact (n:int) : int =
  fact_body fact n
```

Notice how easy it is now to reuse the body of fact but print out intermediate
results after every intermediate call to fact.

```
let rec printing_fact (n:int) : int =
  let result = fact_body printing_fact n in
  print_int result; print_newline();
  result
```

Try out that code to make sure you understand it. Recall also that this is a
very similar technique to what we used in the evaluator code in earlier lectures
and in Assignment 4. Search through that code and near the bottom you will see
the function `eval_body` and `eval` and `debug_eval`. All three are closely
related to our variants of factorial.

### Question 4.3

In `fib.ml`, finish the structure `AutoMemoedFib` using your `Memoizer` functor.
This will let you test your `Memoizer` structure to make sure that you solved
the problem. The Fibonacci implementation produced by your `Memoizer` function
should be very nearly as fast as the hand-rolled version in `MemoedFibo`.

**Rhetorical question:** (Don't hand in an answer but discuss with your
classmates, prof or TA) What happens if you use `Memoizer` to memoize a function
that has effects? In particular, what happens if you memoize a function that
prints things?

### Application: Genome Sequencing

The speed up from memoization can be huge. A good practical example can be found
in genetics: in sequencing a genome, one needs to find the longest common
subsequence between two sequences to get a rough idea of the amount of shared
information between them. For example, a longest common subsequence of AGATT and
AGTCCAGT is AGTT; AGAT is another.

More precisely, a list `l` is a subsequence of `l′` iff `l` can be obtained by
deleting some of the elements of `l′`:
- `[]` is a subsequence of `l` for any `l`.
- `x::xs` is a subsequence of `y::ys` iff either `x::xs` is a subsequence of
    `ys` (delete `y`) or `x = y` and `xs` is a subsequence of `ys` (use y to
    match x).

Given two lists `l1` and `l2`, a list `l` is a longest common subsequence of
`l1` and `l2` iff `l` is a subsequence of `l1` and `l` is a subsequence of `l2`
and `l` is at least as long as any other subsequence of both `l1` and `l2`. If
DNA base-pairs are represented by the type `Base.t`, and DNA strands by the type
`Base.t list`, a very straight forward program to find such longest common
subsequences is

```
type base = Base.base
type dna = Base.dna

let rec slow_lcs ((s1,s2) : dna * dna) : dna =
  match (s1,s2) with
      ([], _) -> []
    | (_, []) -> []
    | (x :: xs, y :: ys) ->
      if Base.eq x y then
      x :: slow_lcs (xs, ys)
      else
      Base.longer_dna_of (slow_lcs (s1, ys)) (slow_lcs (xs, s2))
```

It’s pretty clear that this program takes exponential time to run. It’s somewhat
less clear, though, that it’s also duplicating a good deal of work. For example,
to find the longest subsequence of `x1::xs` and `y1::ys`, we might have to look
at both `(x1::xs, ys)` and `(xs, y1::ys)`. Both of these likely contain
`(xs, ys)` as a subproblem.

### Question 4.4

Use the `Memoizer` functor you’ve defined above to build a version of `lcs`
called `fast_lcs` that avoids computing subproblems more than once.

### Question 4.5

Create a *very simple* experiment that demonstrates the speed up gained from
memoizing `lcs`. Run that experiment in main and have main print out something
informative that demonstrates the speedup. Explain what you have done in a brief
comment in the code.

## Handin Instructions

You may do this problem set in pairs. If you do so, both students are
responsible for all components of the assignment, both students will earn the
same grade and accrue the same number of late days.

Your assignment will be automatically submitted every time you push your changes
to your GitHub repository. Within a couple minutes of your submission, the
autograder will make a comment on your commit listing the output of our testing
suite when run against your code. **Note that you will be graded only on your
changes to `queue.txt`, `streams.ml`, <!-- `queue.ml`, --> `fib.ml`,
`memoizer.ml`, and `lcs.ml`**, and not on your changes to any other files.

You may submit and receive feedback in this way as many times as you like,
whenever you like.

## Acknowledgements

Assignment components drawn from work by Bob Harper and Dan Licata (then-CMU,
now Wesleyan) and Greg Morrisett (then-Harvard, now Cornell).
