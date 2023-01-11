// variables
//   (x:bool)
//   (y:bool)
//   (z:bool) : bool
//
// primitive my_and (a:bool) (b:bool) : bool := a and b
//
// primitive my_or  (a:bool) (b:bool) : bool := a or b
//
// primitive my_not (a:bool) : bool := not a
//
// primitive get_x : bool := x
//
// primitive get_y : bool := y

// primitive get_z : bool := z


// example {x := true; y := false; z := true} -> false
// example {x := false; y := true; z := false} -> true
// example {x := false; y := false; z := true} -> true



// variables
//   (x0:bool) (x1:bool) (x2:bool) (x3:bool)
//   (x4:bool) (x5:bool) (x6:bool) (x7:bool)
//   (y0:bool) (y1:bool) (y2:bool) (y3:bool)
//   (y4:bool) (y5:bool) (y6:bool) (y7:bool) :
//   (bool, bool, bool, bool, bool, bool, bool, bool,)
//
// primitive mk_tuple
//   (a0:bool) (a1:bool) (a2:bool) (a3:bool)
//   (a4:bool) (a5:bool) (a6:bool) (a7:bool) :
//   (bool, bool, bool, bool, bool, bool, bool, bool,)
//   := (a7, a6, a5, a4, a3, a2, a1, a0,)
//
// primitive get_true : bool := true
// primitive get_false : bool := false
//
// primitive get_x0 : bool := x0
// primitive get_x1 : bool := x1
// primitive get_x2 : bool := x2
// primitive get_x3 : bool := x3
// primitive get_x4 : bool := x4
// primitive get_x5 : bool := x5
// primitive get_x6 : bool := x6
// primitive get_x7 : bool := x7
//
// primitive get_y0 : bool := y0
// primitive get_y1 : bool := y1
// primitive get_y2 : bool := y2
// primitive get_y3 : bool := y3
// primitive get_y4 : bool := y4
// primitive get_y5 : bool := y5
// primitive get_y6 : bool := y6
// primitive get_y7 : bool := y7
//
// primitive get_xor (a:bool) (b:bool) : bool := a xor b
// primitive get_and (a:bool) (b:bool) : bool := a and b
// primitive get_or  (a:bool) (b:bool) : bool := a or b
//
// primitive get_not (a:bool) : bool := not a
//
// goal
//   let c0 := false in
//
//   let c1 := (x0 and y0) or (c0 and (x0 or y0)) in
//   let r0 := c0 xor x0 xor y0 in
//
//   let c2 := (x1 and y1) or (c1 and (x1 xor y1)) in
//   let r1 := c1 xor x1 xor y1 in
//
//   let c3 := (x2 and y2) or (c2 and (x2 xor y2)) in
//   let r2 := c2 xor x2 xor y2 in
//
//   let c4 := (x3 and y3) or (c3 and (x3 xor y3)) in
//   let r3 := c3 xor x3 xor y3 in
//
//   let c5 := (x4 and y4) or (c4 and (x0 xor y4)) in
//   let r4 := c4 xor x4 xor y4 in
//
//   let c6 := (x5 and y5) or (c5 and (x5 xor y5)) in
//   let r5 := c5 xor x5 xor y5 in
//
//   let c7 := (x6 and y6) or (c6 and (x6 xor y6)) in
//   let r6 := c6 xor x6 xor y6 in
//
//   let r7 := c7 xor x7 xor y7 in
//
//   (r7, r6, r5, r4, r3, r2, r1, r0,)

variables
  (x0: bool)
  (x1: bool)
  (x2: bool)
  (x3: bool)
  : bool

primitive get_and (a: bool) (b: bool) : bool := a and b
primitive get_or  (a: bool) (b: bool) : bool := a or  b
primitive get_not (a: bool) : bool := not a

primitive get_x0 : bool := x0
primitive get_x1 : bool := x1
primitive get_x2 : bool := x2
primitive get_x3 : bool := x3

goal
  x0 and ((x1 or x2) and (x0 xor x3))
