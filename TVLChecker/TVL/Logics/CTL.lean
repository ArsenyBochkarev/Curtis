import TVLChecker.TVL.AtomicProposition

-- CTL formula syntax tree
inductive CTL where
  | top                                   -- true
  | ap (p : AtomicProposition)            -- atomic predicate
  | not (phi : CTL)                       -- logical NOT
  | and (phi1 phi2 : CTL)                 -- logical AND
  | ex (phi : CTL)                        -- Exists Next (some next step satisfies phi)
  | eu (phi1 phi2 : CTL)                  -- Exists Until (some path keeps phi1 until phi2)
  | eg (phi : CTL)                        -- Exists Global (some path satisfies phi forever)
  deriving BEq, Hashable

-- Syntactic sugar for "eventually": EF phi = E[ true U phi ]
def EF (phi : CTL) : CTL := CTL.eu CTL.top phi
