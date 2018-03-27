# interpreter-rank2-type-infer
OCaml-like interpreter with rank 2 type inferrer.
The type inferrer is an implementation of Kfoury, Assaf J., and Joe B. Wells. "A direct algorithm for type inference in the rank-2 fragment of the second-order calculus." ACM SIGPLAN Lisp Pointers 7.3 (1994): 196-207.


## Example

```ocaml
    # (fun f -> f 1 + f true);;
    - : (forall a. a) -> int = <fun>
    # (fun f -> f 1 + f true) (fun x -> 5);;
    - : int = 10
```

