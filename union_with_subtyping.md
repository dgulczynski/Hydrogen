# Union with subtyping

<img src="https://render.githubusercontent.com/render/math?math=\dfrac{\tau_1' \lessdot \tau_1  \quad  a \lessdot a'  \quad \tau_2 \lessdot \tau_2'}{\tau_1 \rightarrow_a \tau_2 \lessdot (\tau_1' \rightarrow_{a'} \tau_2')}">

```
union (t1 -{a}-> t2) (t1' -{a'}-> t2') =
    union t1' t1 ;
    union t2 t2' ;
    union a a'
```

<img src="https://render.githubusercontent.com/render/math?math=\dfrac{}{\iota \lessdot e}">

<img src="https://render.githubusercontent.com/render/math?math=\dfrac{a \subseteq e \quad a' \lessdot e}{(a \circ a') \lessdot e}">

<img src="https://render.githubusercontent.com/render/math?math=\dfrac{{?u} := \iota }{{?u} \lessdot \iota}">
 
<img src="https://render.githubusercontent.com/render/math?math=\dfrac{a\cap b = \emptyset \quad \text{fresh}(?u)\quad {?v} := (a \circ {?u}) \quad a' \lessdot (b \circ a \circ {?u}) }{(a \circ a') \lessdot (b \circ {?v})}">

<img src="https://render.githubusercontent.com/render/math?math=\dfrac{{?u} := b' \quad b' \lessdot b}{{?u} \lessdot b}">

```
union  []       e        = () 
      (a . a')  e        = union (a . e')
       ?u       []       = ?u := []
       
      (a . a')  (b . ?v) = ?v := a . fresh () ; union a' (b . ?v)

       ?u      (b . ?v)  = add_constraint (?u, b . ?v) (* resolve later *) 
       ?u       b        = add_constraint (?u, b)      (* resolve later *) 
       a        b        = raise (Illtyped (a ^ "does not subtype" ^ b))
```

```
infer (App e1 e2) =
    let t1, eff1 = infer e1
    and t2, eff2 = infer e2  
    and t'       = fresh_type () 
    and eff      = fresh_eff  () 
    and eff'     = fresh_eff  () in
        union (t1, t2 -{eff}-> t') ;
        union eff1 eff' ;
        union eff  eff' ;
        union eff2 eff' ;
        (t', e'')
```

TODO:
 * jeżeli zmienna jest tylko kowariantna (nie występuje _po żadnej lewej stronie_), to można ją zunifikować z pustym efektem
 * zmienne w efektach polimorficznych jeśli występują po lewej muszą wystąpić po prawej


