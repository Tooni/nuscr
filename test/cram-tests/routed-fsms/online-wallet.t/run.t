Generate FSM for OnlineWallet protocol, for Customer role.
  $ nuscr OnlineWallet.nuscr --routed_fsm=Customer@Wallet@OnlineWallet
  digraph G {
    0;
    2;
    3;
    5;
    6;
    8;
    9;
    11;
    
    
    0 -> 2 [label="l12", ];
    2 -> 3 [label="l23", ];
    3 -> 0 [label="l120", ];
    3 -> 5 [label="l45", ];
    3 -> 9 [label="l139", ];
    5 -> 6 [label="l56", ];
    6 -> 8 [label="l78", ];
    6 -> 11 [label="l1011", ];
    8 -> 9 [label="l89", ];
    11 -> 9 [label="l119", ];
    
    }
  json:
  
  {
  "mandatory": ["Customer","Wallet"],
  "optional": ["Vendor"],
  "froms": {"l12": "S0","l23": "S2","l120": "S3","l45": "S3","l139": "S3","l56": "S5","l78": "S6","l1011": "S6","l89": "S8","l119": "S11"},
  "rec_exprs": {
  "try": {"typevar": "AuthLoop", "sort": "number", "refinement": "", "init": "0"}
  }, 
  "edges": {
  "l89": {
  "op": "!",
  "role": "Vendor",
  "label": "pay",
  "payloads": [{
  "name": "payment",
  "sort": "number",
  "refinement": {"binop": "=",
  "e1": "payment",
  "e2": "bill"}
  }],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l78": {
  "op": "!",
  "role": "Wallet",
  "label": "authorise",
  "payloads": [],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l119": {
  "op": "!",
  "role": "Vendor",
  "label": "reject",
  "payloads": [],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l1011": {
  "op": "!",
  "role": "Wallet",
  "label": "reject",
  "payloads": [],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l56": {
  "op": "?",
  "role": "Vendor",
  "label": "request",
  "payloads": [{
  "name": "bill",
  "sort": "number",
  "refinement": {"binop": "<",
  "e1": "bill",
  "e2": "0"}
  }],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l45": {
  "op": "?",
  "role": "Wallet",
  "label": "login_ok",
  "payloads": [],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l120": {
  "op": "?",
  "role": "Wallet",
  "label": "login_retry",
  "payloads": [{
  "name": "msg",
  "sort": "string",
  "refinement": {"binop": "<",
  "e1": "try",
  "e2": "3"}
  }],
  "silents": [],
  "rec_expr_updates": {"try": {"binop": "+",
  "e1": "try",
  "e2": "1"}},
  "tv_resets": []
  },
  "l139": {
  "op": "?",
  "role": "Wallet",
  "label": "login_denied",
  "payloads": [{
  "name": "msg",
  "sort": "string",
  "refinement": {"binop": "=",
  "e1": "try",
  "e2": "3"}
  }],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l23": {
  "op": "!",
  "role": "Wallet",
  "label": "pin",
  "payloads": [{
  "name": "pin",
  "sort": "number",
  "refinement": {"binop": "&&",
  "e1": {"binop": ">=",
  "e1": "pin",
  "e2": "1000"},
  "e2": {"binop": "<",
  "e1": "pin",
  "e2": "10000"}}
  }],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l12": {
  "op": "!",
  "role": "Wallet",
  "label": "login",
  "payloads": [{
  "name": "account",
  "sort": "number",
  "refinement": {"binop": "&&",
  "e1": {"binop": ">=",
  "e1": "account",
  "e2": "100000"},
  "e2": {"binop": "<",
  "e1": "account",
  "e2": "1000000"}}
  }],
  "silents": [],
  "rec_expr_updates": {},
  "tv_resets": []
  }
  }
  }
