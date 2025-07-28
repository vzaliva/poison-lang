def joinStringsWith (s1 : String) (s2 : String) (s3 : String) : String :=
     String.append s2 (String.append s1 s3)
#eval joinStringsWith ", " "one" "and another"
#check joinStringsWith ": "

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

def a:= RectangularPrism.mk 1.1 2.2 3.3
#eval {a with depth:= 10.0}

structure Segment where
  a : Float
  b : Float
deriving Repr

def length (s : Segment) : Float :=
 Float.abs (s.a - s.b)

#eval length (Segment.mk (-1.1) 2.2)
