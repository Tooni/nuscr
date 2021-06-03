Sending a message from the selector to a previously active role in only one branch should throw a user-error.
  $ nuscr BranchErrorPrevious.nuscr --routed_fsm=C@A@BranchErrorPrevious
  nuscr: User error: In a choice, each previously active role must be present in all of the branches. In the latter case, the first message the role receives must be distinct and from the selector. Detected for selector C and previously active role S
  [1]
