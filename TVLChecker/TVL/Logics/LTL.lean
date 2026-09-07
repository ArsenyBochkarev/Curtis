import TVLChecker.TVL.AtomicProposition

inductive LTL where
  | top
  | ap (p : AtomicProposition)
  | not (f : LTL)
  | and (f1 f2 : LTL)
  | next (f : LTL)        -- X f
  | until_ (f1 f2 : LTL)  -- f1 U f2
  deriving BEq, Hashable

abbrev Atom := List LTL

-- Syntactic sugar: F phi = "eventually phi", G phi = "always phi"
def F (f : LTL) : LTL := LTL.until_ LTL.top f
def G (f : LTL) : LTL := LTL.not (F (LTL.not f))
