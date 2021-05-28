Generate FSM for Travel protocol, for role C.
  $ nuscr Travel.nuscr --routed_fsm=C@A@TravelFlattened
  digraph G {
    0;
    3;
    6;
    7;
    8;
    
    
    0 -> 3 [label="l23", ];
    0 -> 6 [label="l56", ];
    0 -> 8 [label="l98", ];
    3 -> 0 [label="l30", ];
    6 -> 7 [label="l67", ];
    7 -> 8 [label="l78", ];
    
    }
  json:
  
  {
  "mandatory": ["A","C"],
  "optional": ["S"],
  "froms": {"l23": "S0","l56": "S0","l98": "S0","l30": "S3","l67": "S6","l78": "S7"},
  "rec_exprs": {
  
  }, 
  "edges": {
  "l30": {
  "op": "?",
  "role": "A",
  "label": "quote",
  "payloads": [{
  "name": "payload_1",
  "sort": "number",
  "refinement": ""
  }],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l23": {
  "op": "!",
  "role": "A",
  "label": "query",
  "payloads": [{
  "name": "payload_1",
  "sort": "string",
  "refinement": ""
  }],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l78": {
  "op": "!",
  "role": "A",
  "label": "accpt",
  "payloads": [{
  "name": "payload_1",
  "sort": "number",
  "refinement": ""
  }],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l67": {
  "op": "?",
  "role": "S",
  "label": "confirm",
  "payloads": [{
  "name": "payload_1",
  "sort": "number",
  "refinement": ""
  }],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l56": {
  "op": "!",
  "role": "S",
  "label": "pay",
  "payloads": [{
  "name": "payload_1",
  "sort": "string",
  "refinement": ""
  }],
  "rec_expr_updates": {},
  "tv_resets": []
  },
  "l98": {
  "op": "!",
  "role": "A",
  "label": "reject",
  "payloads": [],
  "rec_expr_updates": {},
  "tv_resets": []
  }
  }
  }
