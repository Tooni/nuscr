The first messages sent from the selector to roles in its branches should be unique.
  $ nuscr NonUniqueBranchStarts.nuscr --routed_fsm=C@A@NonUniqueBranchStarts
  nuscr: User error: In a choice, each previously active role must be present in either none or all of the branches. In the latter case, the first message the role receives must be distinct and from the selector. Detected for selector C and previously active role A
  [1]
