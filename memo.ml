
let fold_left f e xs =
  let rec g xs ret =
    match xs with
    | [] -> ret
    | x::xs -> g xs (f ret x)
  in g xs e

let rec foldl f e xs =
  match xs with
  | [] -> e
  | x::xs -> f (foldl f e xs) x

let hoge f e x =
  let rec g x ret = f ret x
  in g x e

let hoge f x = let g = f x in g

