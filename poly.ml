open Expr

(* Sum type to encode efficiently polynomial expressions *)
type pExp =
  | Term of int*int (*
      First int is the constant
      Second int is the power of x 
      10  -> Term(10,0)
      2x -> Term(2,1)
      3x^20 -> Term(3, 20)
    *)
  | Plus of pExp list
  (*
    List of terms added
    Plus([Term(2,1); Term(1,0)])
  *)
  | Times of pExp list (* List of terms multiplied *)



let boolAnd (b:bool)(a:bool) : bool=
  if a then
    if b then
      true
    else
      false
  else
    false 

(*
  Function to traslate betwen AST expressions
  to pExp expressions
*)


(* 
  Compute degree of a polynomial expression.

  Hint 1: Degree of Term(n,m) is m
  Hint 2: Degree of Plus[...] is the max of the degree of args
  Hint 3: Degree of Times[...] is the sum of the degree of args 
*)

(* let max (a:int) (b:int): int =
  if a > b then a else b *)


(* Print a pExpr nicely 
  Term(3,0) -> 3
  Term(5,1) -> 5x 
  Term(4,2) -> 4x^2
  Plus... -> () + () 
  Times ... -> ()() .. ()

  Hint 1: Print () around elements that are not Term() 
  Hint 2: Recurse on the elements of Plus[..] or Times[..]
*)
let rec print_pExp (_e: pExp): unit =
  (* TODO *)
  match _e with
    | Term(m,n) ->( 
      match m with
        | 1 ->(
          match n with
            | 0 -> Printf.printf "%d" 1
            | 1 -> Printf.printf "x";
            | _ ->(
              Printf.printf "x^"; 
              Printf.printf "%d" n;
            )
            
        )
         
        | _ ->(
          match n with
            | 0 -> Printf.printf "%d" m;
            | 1 ->(
              Printf.printf "%d" m;
              Printf.printf "x";
            ) 
            | _ -> (
              Printf.printf "%d" m;
              Printf.printf "x^"; 
              Printf.printf "%d" n;
            )
          
        )
    )
    | Times(expL) ->(

      Printf.printf "(";

      for i=0 to (List.length expL)-1 do
        print_pExp (List.nth expL i);
        let temp = (List.length expL)-1 in
        if i<temp then Printf.printf "*"
        else Printf.printf ")"
      done

      

      
    )
    | Plus(expL) ->(

      Printf.printf "(";

      for i=0 to (List.length expL)-1 do
        print_pExp (List.nth expL i);
        let temp = (List.length expL)-1 in
        if i<temp then Printf.printf "+"
        else Printf.printf ")"

      done


    )
    let rec negative (_e:pExp) :pExp = 
      match _e with
      | Term(m,n) -> Term(-m,n)
      | Plus(pl) -> Plus(List.map negative pl)
      | Times(tl) -> negative( simplify (Times(tl)))

    and expand (_e:pExp)(expL:pExp list)(s:int) :pExp =
      let listSize = List.length expL in
      
      if (List.length expL = s) then
        Times(expL)
      else
        (expand _e ([_e]@expL) s)

    and from_expr (_e: Expr.expr) : pExp =

      match _e with
        | Num(i) -> Term(i,0)
        | Var(c) -> Term(1,1)
        | Pow(a,b) -> (
            match a with
              | Var(c) -> Term(1,b)
              | Add(c,d) -> (expand (from_expr(Add(c,d))) [] b)
              | Sub(c,d) -> (expand (from_expr(Sub(c,d))) [] b)
              | Mul (c,d) -> (expand (from_expr(Mul(c,d))) [] b)
              
        )
        | Mul(a,b) -> (
          let first = from_expr a in
          let second = from_expr b in
    
          match first with
            | Times(pl) -> (
              match second with 
                | Times(pl2) ->
                    Times(List.sort compare (List.append pl pl2))
                | _ -> Times(List.sort compare (List.append pl [second]))
    
            )
            | _ ->(
              match second with 
              | Times(pl2) ->
                  Times(List.sort compare (List.append pl2 [first]))
              | _ -> Times(List.sort compare [first;second])
    
            )
      )
        | Add(a,b) -> (
            let first = from_expr a in
            let second = from_expr b in
    
            match first with
              | Plus(pl) -> (
                match second with 
                  | Plus(pl2) ->
                      Plus(List.sort compare (List.append pl pl2))
                  | _ -> Plus(List.sort compare (List.append pl [second]))
    
              )
              | _ ->(
                match second with 
                | Plus(pl2) ->
                    Plus(List.sort compare (List.append pl2 [first]))
                | _ -> Plus(List.sort compare [first;second])
    
              )
        )
        | Sub(a,b) ->(
          let first = from_expr a in
          let second = from_expr b in
  
          match first with
            | Plus(pl) -> (
              match second with 
                | Plus(pl2) ->
                    Plus(List.sort compare (List.append pl (List.map negative pl2)))
                | _ -> Plus(List.sort compare (List.append pl (List.map negative [second])))
  
            )
            | _ ->(
              match second with 
              | Plus(pl2) ->
                  Plus(List.sort compare (List.append (List.map negative pl2) [first]))
              | _ -> Plus (List.sort compare [first; (negative second)])
  
            )



        )
        | Neg(e) -> from_expr(Sub(Num(0),e))
        | Pos(e) -> from_expr(Add(Num(0),e))
        | _ ->
        Term(0,0) 

and degree (_e:pExp): int =  
match _e with 
    | Term(n,m) -> m
    | Plus(p) -> (
    match p with 
      | [] -> 0
      | hd::rest -> (let a = (degree hd) in
          let b = degree (Plus(rest)) in
          if (a>b) then 
            a 
          else
            b
          )
    )
    | Times(t) -> (
      match t with
        | [] -> 0
        | hd::rest -> (let a = (degree hd) in
            let b = degree (Times(rest)) in
            (a+b)
        )
    )
      


(* 
  Comparison function useful for sorting of Plus[..] args 
  to "normalize them". This way, terms that need to be reduced
  show up one after another.
*)
and compare (e1: pExp) (e2: pExp) : int =
  if(degree e1 < degree e2) then 1 else 0

and equalDegrees (e1: pExp) (e2: pExp) : bool =
  if(degree e1 = degree e2) then true else false

  (**)
and indyDegree (e:pExp): bool =
      match e with
        | Plus(pl) ->
          match pl with
            | a::b ->(
            match a with
              |Term(m,n)-> (
                match b with
                  | []-> false
                  | c::d -> 
                  match c with
                    | Term(m,n) ->(
                      if(equalDegrees a c) then true
                      else indyDegree( Plus(b))
                    )
                    | _ -> true
              )
              | _ -> true
            )
            | [] -> true


(* 
  Function to simplify (one pass) pExpr

  n1 x^m1 * n2 x^m2 -> n1*n2 x^(m1+m2)
  Term(n1,m1)*Term(n2,m2) -> Term(n1*n2,m1+m2)

  Hint 1: Keep terms in Plus[...] sorted
  Hint 2: flatten plus, i.e. Plus[ Plus[..], ..] => Plus[..]
  Hint 3: flatten times, i.e. times of times is times
  Hint 4: Accumulate terms. Term(n1,m)+Term(n2,m) => Term(n1+n2,m)
          Term(n1, m1)*Term(n2,m2) => Term(n1*n2, m1+m2)
  Hint 5: Use distributivity, i.e. Times[Plus[..],] => Plus[Times[..],]
    i.e. Times[Plus[Term(1,1); Term(2,2)]; Term(3,3)] 
      => Plus[Times[Term(1,1); Term(3,3)]; Times[Term(2,2); Term(3,3)]]
      => Plus[Term(2,3); Term(6,5)]
  Hint 6: Find other situations that can arise
*)
and simplify1 (e:pExp): pExp =
    match e with
      | Term(m,n)-> e
      | Plus(pl) -> (
        match pl with
          | a::b -> (
            match a with
              | Plus(pl2) -> Plus(List.sort compare (List.append pl2 b))
              | Times(tl) -> Plus(List.sort compare (List.append [(simplify1 (Times(tl)))] b))
              | Term(m,n) ->
                match b with
                  | [] -> Term(m,n)
                  | c::d ->
                    match c with
                      | Term(m1,n1) -> (
                          if (n=n1) then
                            Plus(List.append [Term(m+m1,n)] d)
                          else
                            if indyDegree(e) then
                              Plus([a;simplify1 (Plus(b))])
                            else
                              e
                            
                      )
                      | Plus(pl2) -> Plus(List.sort compare (pl2@[a]@d))
                      | Times(tl) ->(
                          let temp = d@[a] in
                          let temp2 = [simplify1 (simplify1 (Times(tl)))] in
                          let newList = temp@temp2 in
                          Plus(List.sort compare newList)
                          
                      )

          )
      )
      | Times(t) -> 
          match t with
          | a::b -> 
            match a with
              | Times(t2) -> Times(List.sort compare b@t2)
              | Term(m,n) ->(
                match b with
                  | [] -> Term(m,n)
                  | c::d->(
                    match c with
                      | Term(m1,n1) -> Times(List.append [Term(m*m1,n+n1)] d)
                      | Plus(pl) ->(
                          match pl with
                            | hd::tl -> (
                              match hd with
                                | Term(m1,n1) ->(
                                    match tl with
                                      | [] -> Times([Term(m*m1,n+n1)]@d)
                                      | _ -> Plus([Term(m*m1,n+n1)]@[Times([Term(m,n)]@[Plus(tl)]@d)])

                                )
                                (* Not correct *)
                                (* | Plus(pl2) -> Times(List.sort compare [Term(m,n);(Plus(pl2@tl))]@d)  *)
                                | Times(t2) -> Times([Term(m,n);Plus([simplify (Times(t2))]@tl)]@d) 
                                
                            )
                            | [] -> Times([a]@d)
                      )
                  )
                  
              )
              | Plus(pl) ->(
                  match b with
                  | [] -> Plus(pl)  
                  | c::d ->(
                      match c with
                        | Term(m,n) ->(
                          match pl with
                          | hd::tl -> (
                            match hd with
                              | Term(m1,n1) ->(
                                  match tl with
                                    | [] -> Times([Term(m*m1,n+n1)]@d)
                                    | _ -> Plus([Term(m*m1,n+n1)]@[Times([Term(m,n)]@[Plus(tl)]@d)])

                              )
                              
                          )
                          | [] -> Times([a]@d)
                        )
                        | Plus(pl2)->(
                          match pl with
                            | hd::tl ->(
                              match hd with
                                |Term(m,n) ->(
                                  match pl2 with
                                    | hd2::tl2 ->
                                      match hd2 with
                                        Term(m1,n1) ->(
                                          match tl with
                                            | []-> Times(List.sort compare [Term(m,n)]@[Plus(pl2)]@d)
                                            | _ -> Times(List.sort compare [Plus([Times([Term(m,n)]@[Plus(pl2)])]@[Times([Plus(tl)]@[Plus(pl2)])])]@d)

                                        )
                                        (* Not correct *)
                                        (* | Plus(pl2) -> Times([Term(m,n)]@[Plus(pl2@tl)]@d)*)
                                        | Times(t2) -> Times([Plus(pl);Plus([simplify (Times(t2))]@tl2)]@d) 
                                )
                                | Times(t2) -> Times(List.sort compare [Plus([simplify1(Times(t2))]@tl)]@b)
                                | Plus(pl3) -> Times([Plus(pl3@tl)]@b)
                                
                            )
                        )
                  )
              )


                      (* | Plus(pl2)->(
                            match hd with
                              |Term(m,n) ->(
                                match pl2 with
                                  | hd2::tl2 ->
                                    match hd2 with
                                      Term(m1,n1) ->(

                                      )
                              )
                        )  *)


(* 
  Compute if two pExp are the same 
  Make sure this code works before you work on simplify1  
*)

and equal_pExp (_e1: pExp) (_e2: pExp) :bool =
  match _e1 with
  | Term(n,m) -> (
    match _e2 with
      | Term(n2,m2) ->(
        boolAnd (n=n2) (m=m2)
      )
      | _ -> false
  )
  | Plus(p) ->(
    match _e2 with
      | Plus(p2) ->(
        if (List.length p = List.length p2 )then 
        
          match p with
            | a::b ->(
              match p2 with
                | c::d -> (
                  match b with
                    | [] -> (equal_pExp a c)
                    | _ -> boolAnd (equal_pExp a c) (equal_pExp (Plus(b)) (Plus(d)))
                )
            )

        else
          false
      )
      | _ -> false

  )
  | Times(t) ->(
    match _e2 with
      | Times(t2) ->(
        if (List.length t = List.length t2 )then 
        
          match t with
            | a::b ->(
              match t2 with
                | c::d -> (
                  match b with
                    | [] -> (equal_pExp a c)
                    | _ -> boolAnd (equal_pExp a c) (equal_pExp (Times(b)) (Times(d)))
                )
            )

        else
          false
      )
      | _ -> false

  )

(* Fixed point version of simplify1 
  i.e. Apply simplify1 until no 
  progress is made
*)    
and simplify (e:pExp): pExp =
    let rE = simplify1(e) in
    
      
      if (equal_pExp e rE) then
        e
      else  
        simplify(rE)




