The updates for a recursive expression should be the same in each place it's updated.
  $ nuscr NonUniformRecExprUpdates.nuscr --routed_fsm=D@A@NonUniformRecExprUpdates
  nuscr: User error: When branches of a choice update a recursion expression. Each branch must update it in the same way. Failed for choice-maker C
  [1]
