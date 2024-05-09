
import Init.Data.Array
import Init.Data.List
import Mathlib.Data.Finset.Basic
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import Std.Classes.BEq
import Mathlib.Data.Rat.Sqrt
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Init.Data.Int.Order
import Mathlib.Data.Real.Basic


open Nat
 -- don't have to prove decidability

--noncomputable scoped
   --every type is equiped with decidable equality and every propositions has an instance of
namespace ratproof
--use finset

structure Point  where
  x : ℚ
  y : ℚ
deriving DecidableEq --,Repr--- cant derive them, need to do them by hand, learn how to declare and define type class instances

--instance : BEq Point where
 -- beq p q := p.x == q.x && p.y == q.y
--#eval Point.mk 0 0 == Point.mk 1 0

--#eval Point.mk 0 0

--#eval Float.sqrt (-1) == Float.sqrt (-1)
--equality is equaiolit of terms in prop, for those terms
--decideable eq implies BEq
-- lessons learn't, didn't define proper API to improve program later
--#check Point.mk 0 0

structure Line  where
  m : ℚ
  c : ℚ
  vert : ℚ := 0
  isvert : Bool := false --isvert is 0 when regular line and 1 when vertical
deriving DecidableEq --,Repr

--instance : BEq Line where
  --beq l j := l.m == j.m && l.c == j.c && l.vert == j.vert && l.isvert == j.isvert

structure Circle where
  a : ℚ
  b : ℚ
  r : ℚ
deriving DecidableEq --,Repr

--instance : BEq Circle where
  --beq c o := c.a == o.a && c.b == o.b && c.r == o.r
--#check { m := 1 , c:= 1 : Line}
--#check { m := 1 , c:= 1 : Line}.m
--#eval { m := 3 , c:= 0 : Line}.m
--#eval Rat.den (1/2)
--#eval Rat.num (1/2) > 0
--#eval Rat.sqrt (-1)
--def l1 := {m:=1,c:=2,vert:=0,isvert:=false : Line}
--def l2 := {m:=1,c:=2,vert:=0,isvert:=false : Line}
--#eval l1==l2

def distancepp (p1 : Point) (p2 : Point) : ℚ :=
  Rat.sqrt (((p2.x - p1.x) ^ 2) + ((p2.y - p1.y) ^ 2))



def origin  : Point := {x := 0.0, y := 0.0}
def origin1 : Point := {x := 1.0, y := 0.0}

--#eval distancepp (Point.mk 0 0) (Point.mk 3 4)


def lined (p : Point) (q: Point): Finset Line :=
  if p.x == q.x then
    if p.y == q.y then
      {}
      else
    {{m := 0 , c:= 0, vert:= p.x, isvert := true}}
  else
    {{m := (p.y - q.y)/(p.x - q.x),
      c := p.y - (p.y - q.y)/(p.x - q.x)*(p.x)}}

def circled (p : Point) ( q : Point) : Finset Circle :=
    if p == q then {} else
      if distancepp p q > 0 then
      {{
      a := p.x
      b := p.y
      r := distancepp p q
      }}
      else {}


--variable (k:ℕ )
--#eval circled (Point.mk k 0) (Point.mk k 0)
--#eval Point.mk k 0 == Point.mk k 0


def linexline (l1 : Line) (l2 : Line): Finset Point :=
  let c1 := l1.c -- lets define some local variables to ease reading
  let c2 := l2.c
  let m1 := l1.m
  let m2 := l2.m

  if l1.isvert == false  && l2.isvert == false  then --we that both lines are non-vertical

    if m1 == m2 then  --if gradients are the same, they are parallel
      {} -- no new points can be created so we return the empty set

    else -- we may now assume the non-vertical lines intersect
      let x1 := (c2 - c1)/(m1 - m2) -- derived from intro to math
      { {x := x1, y := m1*x1 + c1} } -- we return the appropriate singleton

  else -- at least one of the gradients is vertical
    if l1.isvert == true then  --suppose the first line is vertical

      if l2.isvert == true then --if the second is also vertical
        {}    --then we have 2 parallel lines, and no new points

      else --here we have that the second line is non-vertical
        { {x := l1.vert, y := m2*l1.vert + c2} } --the lines must intersect, so we return the appropriate singleton

    else -- we know the second line is vertical
      { {x := l2.vert, y := m1*l2.vert + c1} }


def quad_formula_pos (a b c : ℚ) : ℚ :=  (-b + Rat.sqrt (( b^2 - 4*a*c ))) / (2*a)

def quad_formula_neg (a b c : ℚ) : ℚ := (-b - Rat.sqrt (( b^2 - 4*a*c ))) / (2*a)

def discriminant (a b c : ℚ) : ℚ := b^2 - 4*a*c

--#eval IsSquare (2:ℚ)


def linexcircle (l : Line) (c : Circle) : Finset Point :=
--we intend to return the empty set, a Point singleton or the finite set of 2 points.

  if l.isvert == false then --suppose the line is non-vertical
    let A := (l.m)^2 + 1
    let B := 2*(l.m*(l.c - c.b) - c.a)        -- see intro-background maths
    let C := c.a^2 + (l.c - c.b)^2 - c.r^2      -- the plugins for the quad formula, as explained in the maths intro

    let x1 := quad_formula_pos A B C

    let x2 := quad_formula_neg A B C  -- calculate the positive and negative values

    let y1 := l.m*(x1) + l.c    -- then we plug in the respective x coordinate to get the y coordinate
    let y2 := l.m*(x2) + l.c
    if IsSquare (discriminant A B C) then -- cos surds on Rationals don't exist
      if (discriminant A B C) == 0 then
        {{ x := x1 , y := y1 }}--    check this later                           Float.isNaN x1 ∨ Float.isNaN x2 ∨ Float.isNaN y1 ∨ Float.isNaN y2 then [origin] --so if the intersections are NaN, then return the origin
      else
        if (discriminant A B C) < 0 then
          {} -- check this too
        else {{ x := x1 , y := y1 : Point }, {x := x2 , y := y2 : Point }} --           point_cleanup [{ x := x1 , y := y1 : Point }, {x := x2 , y := y2 : Point }]
    else {} -- want to return empty set when not a square

  else --assume the line is vertical
    if c.r^2 ≤ (l.vert - c.a)^2 then --                                ( (c.a - c.r) ≤ l.x ) ∧ ( l.x ≤ ( c.a + c.r) ) then --here we check if the vertical line is within the circle, if so, solve for y, else return origin.
      let yy1 := (c.b + Rat.sqrt ((c.r^2 )- (l.vert - c.a)^2)) -- see intro-background maths
      let yy2 := (c.b - Rat.sqrt ((c.r^2 )- (l.vert - c.a)^2))
      let p := {x := l.vert, y:= yy1 : Point}
      let q := {x := l.vert, y:= yy2 : Point}
      if IsSquare ((c.r^2 )- (l.vert - c.a)^2) then
        if p == q then {p} else {p,q}  -- if the points are the same, return one to avoid repetitions.


      else {} --Rat doesn't eval surds, so must return empty string
    else {}

#eval Nat.zero
#eval {x:=1 , y:=1 : Point}.x
#eval (3:ℚ)/ 4 / 5 / 7

/-
-------test linexcircle
--def ll := {m:= 0, c:= 0, vert:=0 : Line}
--def cc := Circle.mk 1 0 1  --- importnatly i get this for inductive Nat proof

------ test membership and theorems
--#eval origin ∈ (linexcircle ll cc)
#eval origin
def myset : Finset ℕ := {1,2,3}
def myset1 : Finset ℕ := {1}
#eval myset.val
#eval myset --removes repeat cases
#eval (linexcircle ll cc)
def p11 := Point.mk 1 1
--------------------zulip q
def my_set : Finset ℕ := {1,2,3}

--#eval (Finset.toList my_set)[0]!
#check lined origin
#eval (linexcircle ll cc) ∪ {p11}


---------------------

def remove_one  (s : List ℕ ) : List ℕ  :=
match s with
  | []  => []
  | x::xs => if x == 1 then [0] else remove_one xs

#eval 1 ∈ myset
def add1 (n :Nat) : Finset ℕ  :=  {n , n+4}
#eval Finset.biUnion myset add1
--

theorem originin : origin ∈ (linexcircle ll cc) := by native_decide ---- holy shit
#eval linexcircle {m:=0,c:=0,isvert := true, vert:= 3.5} {a:=4,b:=0,r:=1}


theorem testt : 1 ∈ myset := by native_decide
-- we now know we can prove 2 is constructable. and from there ℕ and ℤ
------end of tests
-/
def distancecc (c1 c2 : Circle) : ℚ :=
  distancepp {x:= c1.a, y:= c1.b : Point} {x:= c2.a, y:= c2.b : Point}


def circlexcircle (c1 : Circle) (c2 : Circle) : Finset Point :=
  let a := c1.a
  let b := c1.b -- lets declare some more familiar local variables to make this more legible
  let r := c1.r
  let u := c2.a
  let v := c2.b
  let s := c2.r
  if a == u ∧ b == v then {} else
  if (!((distancecc c1 c2) > r + s) ) ∧ !( ((distancecc c1 c2) + r < s) ∨ ((distancecc c1 c2) + s < r) ) then -- compare radiuses to disnace to see if intersect
    if (v != b) then -- remember to consider when they circles share the same y coordinate
      let m' := -(u - a) / (v - b)
      let c' := (-a^2 - b^2 + r^2 + u^2 + v^2 - s^2) / (2*(v - b))
      let l1 := {m := m' , c := c' : Line}
      linexcircle l1 c1 --return the points from our prevoius function

    else  -- now suppose the circles share the same y coordinate for the centre

        if (u == a) then {} --if the circles have the same origin, regardless of the radius, no new points are created
        else -- now we may assume the circles intersect, where the line that connects the intersections is a vertical line.

          let x' := (r^2 - s^2 - a^2 + u^2) / (2*(u - a)) -- derived from the intro to math eq
          let l2 := {m:=0 ,c:= 0, vert := x', isvert := true : Line}

          linexcircle l2 c1 --uses the linexcircle equation we stated earlier
  else {} -- the circles don't intersect

--no cleanup needed
--now we want to individually call each element in finset and make calculations to it

--- step 1 funcion which turns set of points into set of lines


--def finset_lined (p q :Point) : Finset Line := lined p q

def linesfrom_p1 (s : Finset Point)  (p1 : Point) := Finset.biUnion s (lined p1 )

def linesfrom_points (ps : Finset Point) : Finset Line := Finset.biUnion ps (linesfrom_p1 ps)

--#eval linesfrom_points ({origin, (Point.mk 0 1), p11, origin1})  --- this function is super valid from ℚ → ℚ

--- step 2 function which turns set of lines into set of points

--def finset_linexline (l1 l2 : Line) : Finset Point := {linexline l1 l2}

def pointsfrom_l1 (s : Finset Line) (l1 : Line) : Finset Point := Finset.biUnion s (linexline l1)

def pointsfrom_lines (ps : Finset Line) : Finset Point := Finset.biUnion ps (pointsfrom_l1 ps)

--- step 3 function which turns set of points to set of circles

--def finset_circled (p q :Point) : Finset Circle := circled p q

def circlesfrom_p1 (s : Finset Point)  (p1 : Point) := Finset.biUnion s (circled p1 )

def circlesfrom_points (ps : Finset Point) : Finset Circle := Finset.biUnion ps (circlesfrom_p1 ps)

--- step 4 function which turns set of circles to set of points

--def finset_circlexcircle (c1 c2 : Circle) : Finset Point := circlexcircle c1 c2 -- already produces finset, no change needed.

def pointsfrom_c1 (s : Finset Circle) (c1 : Circle) : Finset Point := Finset.biUnion s (circlexcircle c1)

def pointsfrom_circles (ps : Finset Circle) : Finset Point := Finset.biUnion ps (pointsfrom_c1 ps)

--- step 5, a function which given a set of lines and circles, it produces the intersections

def pointsfrom_l1xcs (cs : Finset Circle) (l1 : Line) : Finset Point := Finset.biUnion cs (linexcircle l1)

def pointsfrom_lsxcs (ls : Finset Line) (cs : Finset Circle) : Finset Point := Finset.biUnion ls (pointsfrom_l1xcs cs)


----------------------now we have all the functions which give all the possible point intersections.
----------lets concstenate them

def points_from_lines_from_points (ps : Finset Point) : Finset Point := pointsfrom_lines (linesfrom_points ps )

def points_from_circles_from_points (ps : Finset Point) : Finset Point := pointsfrom_circles (circlesfrom_points ps)

def points_from_linexcircle_from_points (ps : Finset Point) : Finset Point :=  pointsfrom_lsxcs (linesfrom_points ps) (circlesfrom_points ps)

def one_step_construction (ps : Finset Point) : Finset Point := ps ∪ (points_from_lines_from_points ps) ∪ (points_from_circles_from_points ps) ∪ (points_from_linexcircle_from_points ps)

---- make one step constructions contain the base given set
--#eval -1 % 5
def S : Finset Point := {origin, origin1}

--def Sx : Finset Point := {Point.mk 4 0, Point.mk 3 0}
/-

#eval Sx
#eval circlesfrom_points Sx
#eval pointsfrom_circles (circlesfrom_points Sx)
#eval points_from_lines_from_points Sx
#eval points_from_circles_from_points Sx
#eval points_from_linexcircle_from_points Sx
#eval one_step_construction Sx
#eval one_step_construction S
#eval points_from_circles_from_points S --surd found, so doesn't evaluate.

-/




-------- lets create a function for multiple itterations of one_step_consgtructinos


def n_step_construction (n : ℕ ) : Finset Point :=
  match n with
  | zero => S
  | succ (n) => one_step_construction (n_step_construction (n))

--#eval n_step_construction (3)

lemma two_constructable : ∃ ( n : ℕ ) , {x:= 2, y:= 0 : Point} ∈ n_step_construction ( n ) :=
  by
  use 1

  native_decide

--axiom constructable (p: Point) : ∃ (n : ℕ) , p ∈ n_step_construction (n) → True

--theorem twoo_constructable : constructable {x:=2,y:=0:Point} → True := by sorry
--#check Finset.union_assoc
--#check Finset.subset_union_left
--#check Finset.mem_smul_finset


def constructable (n : ℕ ) : Prop := ∃ (k:ℕ ), { x := n, y := 0 } ∈ n_step_construction k


end ratproof
