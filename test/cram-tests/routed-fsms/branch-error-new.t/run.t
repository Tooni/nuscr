A newly active role's first interaction not being the receiving of a message from the selector throws a user-error.
  $ nuscr BranchErrorNew.nuscr --routed_fsm=C@A@BranchErrorNew
  nuscr: User error: In a choice, each newly active role must receive a distinct message from the selector. Violation detected for selector C, in the branch that activates role(s): S
  [1]
