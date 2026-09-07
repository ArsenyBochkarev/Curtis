import TVL.Sema
import Engine.CTL

-- TODO

def dummyInitialState : State :=
  -- A sample state: empty queues, start PCs for a couple of actors and
  -- their IR graphs.
  {
    queues := []
    guardVars := []
    actorThreads := [("Actor1", ([0], none)), ("Actor2", ([0], none))]
    actorGraphs := [] -- fill in with test instructions
  }

def main : IO Unit := do
  IO.println "Running the TVL Model Checker..."

  -- Generate the state graph
  let graph := generateGraph dummyInitialState

  IO.println "Graph generation complete!"
  IO.println s!"States found: {graph.states.length}"
  IO.println s!"Transitions found: {graph.forwardEdges.length}"
