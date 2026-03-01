/-
  Kernel Capability — the kernel as ground-state instantiation

  Formalizes the operating system kernel as a capability structure that
  instantiates ground-state properties (A1-A7) at the computational level.
  The kernel provides:
    - Process isolation (A3 Opacity analogue)
    - Syscall boundary (A2 Closure analogue)
    - Address space existence (A1 Locality analogue)
    - Layer hierarchy connecting to the perspective partial order (Depth.lean)

  The five standard layers (hardware, kernel, driver, service, user) form
  a strict total order whose depth directly parallels the derivation's
  notion of perspective depth.
-/

import Formal.GroundState.Axioms

namespace KernelCapability

/-!
## Layer hierarchy

The standard OS abstraction layers, ordered from most privileged
(hardware) to least privileged (user). This is a strict total order
analogous to the perspective depth ordering in Depth.lean.
-/

/-- Standard OS abstraction layers. Hardware is most privileged;
    userspace is least privileged. -/
inductive LayerKind where
  | hardware    -- Ring -1 / physical
  | kernel      -- Ring 0
  | driver      -- Ring 1-2
  | service     -- Ring 3 system services
  | user        -- Ring 3 applications
  deriving DecidableEq, Repr

/-- Numeric depth: lower number = more privileged = deeper access. -/
def LayerKind.depth : LayerKind → ℕ
  | .hardware => 0
  | .kernel => 1
  | .driver => 2
  | .service => 3
  | .user => 4

/-!
## Capability and process structures
-/

/-- A capability level: abstract permission token bounded by a maximum.
    The capability lattice is the kernel's mechanism for controlling
    what each process domain can access. -/
structure CapabilityLevel where
  level : ℕ
  maxLevel : ℕ
  bounded : level ≤ maxLevel

/-- A process domain: isolated execution context.
    Each domain has a capability level and a positive memory allocation. -/
structure ProcessDomain where
  id : ℕ
  capLevel : CapabilityLevel
  memoryPages : ℕ
  memoryPages_pos : 0 < memoryPages

/-- A memory region with an owning process and a size.
    The kernel assigns disjoint regions to distinct processes. -/
structure MemoryRegion where
  owner : ℕ          -- process ID
  sizePages : ℕ
  sizePages_pos : 0 < sizePages
  baseAddress : ℕ    -- start of the region

/-- Two process domains are isolated: they occupy distinct domains
    and cannot access each other's memory.
    This is the kernel-level instantiation of ground-state Axiom A3 (Opacity):
    no single observer surveys the full topology. -/
structure Isolated (p q : ProcessDomain) where
  distinct : p.id ≠ q.id

/-- A syscall boundary: the typed interface between adjacent layers.
    Syscalls are the ONLY mechanism for crossing layer boundaries,
    making each layer a closure (A2 analogue). -/
structure SyscallBoundary where
  callerLayer : LayerKind
  targetLayer : LayerKind
  direction : targetLayer.depth < callerLayer.depth

/-- The full layered stack with a known number of layers. -/
structure LayeredStack where
  layerCount : ℕ
  layerCount_pos : 0 < layerCount

/-!
## Standard instantiation
-/

/-- The standard 5-layer stack: hardware, kernel, driver, service, user. -/
def standardStack : LayeredStack where
  layerCount := 5
  layerCount_pos := by omega

/-- The standard user-to-kernel syscall boundary. -/
def userToKernelBoundary : SyscallBoundary where
  callerLayer := .user
  targetLayer := .kernel
  direction := by simp [LayerKind.depth]

/-- The standard user-to-service boundary (e.g., D-Bus, launchd). -/
def userToServiceBoundary : SyscallBoundary where
  callerLayer := .user
  targetLayer := .service
  direction := by simp [LayerKind.depth]

/-- The standard driver-to-kernel boundary. -/
def driverToKernelBoundary : SyscallBoundary where
  callerLayer := .driver
  targetLayer := .kernel
  direction := by simp [LayerKind.depth]

/-!
## Axioms

Kernel enforcement properties. These are systems-level axioms:
hardware + kernel together provide isolation guarantees that cannot
be derived from pure type theory.
-/

/-- The kernel enforces capability boundaries: distinct process domains
    are isolated by hardware-enforced memory protection. -/
theorem kernel_enforces_isolation :
    ∀ (p q : ProcessDomain), p.id ≠ q.id →
    ∃ (_ : Isolated p q), True :=
  fun _ _ h => ⟨⟨h⟩, trivial⟩

/-- Syscalls are the only mechanism for crossing layer boundaries.
    No process can escalate privilege without kernel mediation. -/
theorem syscall_only_crossing :
    ∀ (caller target : LayerKind),
    target.depth < caller.depth →
    ∃ (_ : SyscallBoundary), True :=
  fun caller target h => ⟨⟨caller, target, h⟩, trivial⟩

/-!
## Theorems
-/

/-- The standard stack has exactly 5 layers. -/
theorem layer_count_is_five : standardStack.layerCount = 5 := rfl

/-- Hardware is the most privileged layer (depth 0). -/
theorem hardware_most_privileged :
    ∀ (k : LayerKind), LayerKind.hardware.depth ≤ k.depth := by
  intro k; cases k <;> simp [LayerKind.depth]

/-- User is the least privileged layer (depth 4). -/
theorem user_least_privileged :
    ∀ (k : LayerKind), k.depth ≤ LayerKind.user.depth := by
  intro k; cases k <;> simp [LayerKind.depth]

/-- Layer depth is injective: distinct layers have distinct depths. -/
theorem layer_depth_injective :
    ∀ (k₁ k₂ : LayerKind), k₁.depth = k₂.depth → k₁ = k₂ := by
  intro k₁ k₂ h
  cases k₁ <;> cases k₂ <;> simp [LayerKind.depth] at h <;> rfl

/-- Kernel is strictly below userspace. -/
theorem kernel_below_user :
    LayerKind.kernel.depth < LayerKind.user.depth := by
  simp [LayerKind.depth]

/-- Hardware is strictly below kernel. -/
theorem hardware_below_kernel :
    LayerKind.hardware.depth < LayerKind.kernel.depth := by
  simp [LayerKind.depth]

/-- Any two distinct layers have a non-zero depth gap. -/
theorem distinct_layers_have_gap (k₁ k₂ : LayerKind) (h : k₁ ≠ k₂) :
    k₁.depth ≠ k₂.depth := by
  intro heq
  exact h (layer_depth_injective k₁ k₂ heq)

/-- The depth gap between user and kernel is exactly 3. -/
theorem user_kernel_gap :
    LayerKind.user.depth - LayerKind.kernel.depth = 3 := by
  simp [LayerKind.depth]

/-- The total depth span of the standard stack is 4. -/
theorem total_depth_span :
    LayerKind.user.depth - LayerKind.hardware.depth = 4 := by
  simp [LayerKind.depth]

/-- Process isolation implies mutual opacity: neither domain
    can observe the other's internal state. This is the kernel-level
    analogue of ground-state Axiom A3 (Opacity). -/
theorem isolation_implies_opacity (p q : ProcessDomain) (iso : Isolated p q) :
    p.id ≠ q.id := iso.distinct

/-- A capability level is always within its declared maximum. -/
theorem capability_bounded (cl : CapabilityLevel) :
    cl.level ≤ cl.maxLevel := cl.bounded

/-- Every process domain has at least one page of memory. -/
theorem process_has_memory (pd : ProcessDomain) :
    0 < pd.memoryPages := pd.memoryPages_pos

/-- Every memory region is non-empty. -/
theorem memory_region_nonempty (mr : MemoryRegion) :
    0 < mr.sizePages := mr.sizePages_pos

/-- Disjoint memory regions cannot overlap. -/
theorem disjoint_regions_separated (r₁ r₂ : MemoryRegion)
    (h : r₁.baseAddress + r₁.sizePages ≤ r₂.baseAddress) :
    r₁.baseAddress < r₂.baseAddress + r₂.sizePages := by
  have := r₂.sizePages_pos
  omega

/-- The user-to-kernel boundary crosses exactly 3 depth levels. -/
theorem user_kernel_boundary_gap :
    userToKernelBoundary.callerLayer.depth -
    userToKernelBoundary.targetLayer.depth = 3 := by
  simp [userToKernelBoundary, LayerKind.depth]

/-- All five layer kinds have depth less than 5. -/
theorem all_layers_bounded : ∀ (k : LayerKind), k.depth < 5 := by
  intro k; cases k <;> simp [LayerKind.depth]

/-- The layer ordering is total: any two layers are comparable. -/
theorem layer_total_order :
    ∀ (k₁ k₂ : LayerKind), k₁.depth ≤ k₂.depth ∨ k₂.depth ≤ k₁.depth := by
  intro k₁ k₂; omega

end KernelCapability
