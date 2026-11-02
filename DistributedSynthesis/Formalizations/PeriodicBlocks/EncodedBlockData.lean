/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanks
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayers
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReplay
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingComponents

/-! Numeric data for fixed-length blocks. All searches are bounded by the
supplied finite alphabets, width and block length. No realizability test is
used to generate these data. -/
namespace Characterisation.PeriodicBlocks.EncodedBlock
open DistributedSynthesis
set_option maxSynthPendingDepth 128
set_option synthInstance.maxSize 2048

abbrev Views := Bool × Bool
abbrev Boundary := List Views × List Nat × List Nat
abbrev Response := List Nat × List Nat
abbrev Move := Boundary × EncodedClosingBanks.Bank × List Response
abbrev Outcome := List Bool × Boundary
/-- Width minus one, block length, graph-state count, objective-state count,
environment count, output count, and the two letter-decoding tables. -/
abbrev Context := Nat × Nat × Nat × Nat × Nat × Nat ×
  List EncodedClosingObservations.Round × List (Nat × Nat)
/-- Context, graph transitions, live-state bits, and objective transitions. -/
abbrev Data := Context × List (List Nat) × List Bool × EncodedParityTables.Data

def width (c : Context) := c.1+1
def depth (c : Context) := c.2.1
def graphs (c : Context) := c.2.2.1
def objectives (c : Context) := c.2.2.2.1
def environments (c : Context) := c.2.2.2.2.1
def outputs (c : Context) := c.2.2.2.2.2.1
def rounds (c : Context) := c.2.2.2.2.2.2.1
def outputPairs (c : Context) := c.2.2.2.2.2.2.2
def layerContext (c : Context) : EncodedClosingLayers.Context :=
  (width c,environments c,depth c)
def endpoints (c : Context) := EncodedClosingLayers.slots (layerContext c)
def endCount (c : Context) := (endpoints c).length

def boundaries (c : Context) : List Boundary :=
  (FiniteSearch.words [(false,false),(false,true),(true,false),(true,true)] (width c*width c)).product
    ((FiniteSearch.words (List.range (graphs c)) (width c)).product (FiniteSearch.words (List.range (objectives c)) (width c)))
def masks (c : Context) := FiniteCodeNumbering.unique (FiniteSearch.words [false,true] (endCount c))
def responses (c : Context) : List Response :=
  (FiniteSearch.words (List.range (endCount c)) (width c)).product (FiniteSearch.words (List.range (width c)) (endCount c))
def banks (c : Context) :=
  FiniteSearch.words (EncodedClosingPlans.plans (environments c,depth c) (outputs c)) (width c)
def moves (c : Context) : List Move :=
  FiniteCodeNumbering.unique
    ((boundaries c).product ((banks c).product (FiniteSearch.words (responses c) (masks c).length)))
def outcomes (c : Context) : List Outcome := FiniteCodeNumbering.unique ((masks c).product (boundaries c))

def bankData (c : Context) (b : Boundary) : EncodedClosingBanks.Data :=
  (width c,(environments c,depth c),rounds c,outputPairs c,b.1)
def endpoint (c : Context) (i : Nat) := (endpoints c).getD i (0,[])
def observed (c : Context) (b : Boundary) (i j : Nat) :=
  EncodedClosingBanks.observed (bankData c b) (endpoint c i) (endpoint c j)
def graphAt (d : Data) (b : Boundary) (s : EncodedClosingLayers.Slot) :=
  s.2.foldl (fun q e => (d.2.1.getD e []).getD q 0) (b.2.1.getD s.1 0)
def objectiveAt (d : Data) (m : Move) (s : EncodedClosingLayers.Slot) :=
  EncodedClosingReplay.replay d.2.2.2 (m.1.2.2.getD s.1 0)
    ((environments d.1,depth d.1),outputs d.1,m.2.1.getD s.1 [],s.2)
def graphEnd (d : Data) (m : Move) (i : Nat) := graphAt d m.1 (endpoint d.1 i)
def objectiveEnd (d : Data) (m : Move) (i : Nat) := objectiveAt d m (endpoint d.1 i)
def live (d : Data) (m : Move) (i : Nat) := d.2.2.1.getD (graphEnd d m i) false

def components (d : Data) (m : Move) : EncodedClosingComponents.Data :=
  (endCount d.1,(List.range (endCount d.1)).flatMap (fun i =>
    (List.range (endCount d.1)).map (fun j => observed d.1 m.1 i j)),
    (List.range (endCount d.1)).map (live d m))
def component (d : Data) (m : Move) (i : Nat) :=
  (List.range (endCount d.1)).map (EncodedClosingComponents.mask (components d m) i)
def response (c : Context) (m : Move) (mask : List Bool) : Response :=
  m.2.2.getD (@List.idxOf (List Bool) instBEqOfDecidableEq mask (masks c)) ([],[])
def folded (r : Response) (i : Nat) := r.1.getD (r.2.getD i 0) 0

def target (d : Data) (m : Move) (mask : List Bool) : Boundary :=
  let keep := (response d.1 m mask).1
  (keep.flatMap (fun i => keep.map (observed d.1 m.1 i)),
    keep.map (graphEnd d m),keep.map (objectiveEnd d m))

def ResponseValid (d : Data) (m : Move) (mask : List Bool) : Prop :=
  let r := response d.1 m mask
  (∀ i ∈ r.1, mask.getD i false = true) ∧
  (∀ i < endCount d.1, ∀ j < endCount d.1,
    mask.getD i false = true → mask.getD j false = true →
      ((observed d.1 m.1 i j).1 = true →
        (observed d.1 m.1 (folded r i) (folded r j)).1 = true) ∧
      ((observed d.1 m.1 i j).2 = true →
        (observed d.1 m.1 (folded r i) (folded r j)).2 = true)) ∧
  (∀ i < endCount d.1, mask.getD i false = true →
    graphEnd d m (folded r i) = graphEnd d m i ∧
    objectiveEnd d m (folded r i) = objectiveEnd d m i)
instance (d : Data) (m : Move) (mask : List Bool) : Decidable (ResponseValid d m mask) := by
  unfold ResponseValid
  dsimp only
  exact @instDecidableAnd _ _ (by infer_instance)
    (@instDecidableAnd _ _ (by infer_instance) (by infer_instance))
def Legal (d : Data) (b : Boundary) (m : Move) : Prop :=
  m.1=b ∧ EncodedClosingBanks.coherent (bankData d.1 m.1) m.2.1 = true ∧
    ∀ i < endCount d.1, live d m i = true → ResponseValid d m (component d m i)
instance (d : Data) (b : Boundary) (m : Move) : Decidable (Legal d b m) := by
  unfold Legal
  infer_instance
def offered (d : Data) (m : Move) (b : Outcome) : Bool :=
  decide (b.2 = target d m b.1 ∧
    ∃ i < endCount d.1, live d m i = true ∧ b.1=component d m i)
def legal (d : Data) (b : Boundary) (m : Move) := decide (Legal d b m)

def color (d : Data) (m : Move) (i : Nat) : Nat :=
  let s := endpoint d.1 i
  FiniteSearch.minWith (EncodedParityTables.priority d.2.2.2 (m.1.2.2.getD s.1 0))
    ((List.range (depth d.1)).map (fun k =>
      EncodedParityTables.priority d.2.2.2 (objectiveAt d m (s.1,s.2.take k))))
def Edge (d : Data) (old : Nat × Nat) (m : Move) (b : Outcome) (next : Nat × Nat) : Prop :=
  offered d m b = true ∧ ∃ i < endCount d.1,
    b.1.getD i false = true ∧ (endpoint d.1 i).1 = old.1 ∧
      (response d.1 m b.1).2.getD i 0 = next.1 ∧ color d m i = next.2
instance (d : Data) (old : Nat × Nat) (m : Move) (b : Outcome) (next : Nat × Nat) :
    Decidable (Edge d old m b next) := by
  unfold Edge
  infer_instance

end Characterisation.PeriodicBlocks.EncodedBlock
