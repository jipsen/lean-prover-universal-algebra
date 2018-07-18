//type variables
A = "A" 
B = "B" 
//constants
a = "a"
b = "b"
c = "c"
d = "d"
e = "e"
//function symbols
f = "f" 
g = "g"
h = "h"
k = "k"
//relation symbols
R = "R" 
S = "S"
//variables
u = "u"
v = "v"
w = "w"
x = "x"
y = "y"
z = "z"
identities = [
 {"name":"involutive",           "formula":[R, [h,[h,x]], x]},
 {"name":"inverse_ops",          "formula":[R, [h,[k,x]], x]},
 {"name":"unary_absorption_l",   "formula":[R, [h,[k,x]], [k,x]]},
 {"name":"unary_absorption_r",   "formula":[R, [h,[k,x]], [h,x]]},
 {"name":"unary_idempotent",     "formula":[R, [h,[h,x]], [h,x]]},
 {"name":"idempotent",           "formula":[R, [f,x,x], x]},
 {"name":"identity_l",           "formula":[R, [f,e,x], x]},
 {"name":"identity_r",           "formula":[R, [f,x,e], x]},
 {"name":"zero_l",               "formula":[R, [f,b,x], b]},
 {"name":"zero_r",               "formula":[R, [f,x,b], b]},
 {"name":"inverse_l",            "formula":[R, [f,[h,x],x], 1]},
 {"name":"inverse_r",            "formula":[R, [f,x,[h,x]], 1]},
 {"name":"const_mult_l",         "formula":[R, [f,c,x], [h,x]]},
 {"name":"const_mult_r",         "formula":[R, [f,x,c], [h,x]]},
 {"name":"square_constant",      "formula":[R, [f,x,x], c]},
 {"name":"square_unary",         "formula":[R, [f,x,x], [h,x]]},
 {"name":"unary_identity_l",     "formula":[R, [f,[h,x],x], x]},
 {"name":"unary_identity_r",     "formula":[R, [f,x,[h,x]], x]},
 {"name":"unary_const_mult_l",   "formula":[R, [h,[f,c,x]], [f,c,[h,x]]]},
 {"name":"unary_const_mult_r",   "formula":[R, [h,[f,x,c]], [f,[h,x],c]]},
 
 {"name":"commutative",          "formula":[R, [f,x,y], [f,y,x]]},
 {"name":"unary_projection_l",   "formula":[R, [f,x,y], [h,x]]},
 {"name":"unary_projection_r",   "formula":[R, [f,x,y], [h,y]]},
 {"name":"idempotent_l",         "formula":[R, [f,x,[f,x,y]], [f,x,y]]},
 {"name":"idempotent_r",         "formula":[R, [f,[f,x,y],y], [f,x,y]]},
 {"name":"idempotent_l'",        "formula":[R, [f,x,[f,y,x]], [f,x,y]]},
 {"name":"idempotent_r'",        "formula":[R, [f,[f,x,y],x], [f,x,y]]},
 {"name":"rectangular_l",        "formula":[R, [f,[f,x,y],x], x]},
 {"name":"rectangular_r",        "formula":[R, [f,x,[f,y,x]], x]},
 {"name":"absorption",           "formula":[R, [g,[f,x,y],x], x]},
 {"name":"absorption'",          "formula":[R, [g,x,[f,y,x]], x]},
 {"name":"division_l",           "formula":[R, [f,x,[g,x,y]], y]},
 {"name":"division_r",           "formula":[R, [f,[g,x,y],y], x]},
 {"name":"division_l'",          "formula":[R, [g,x,[f,x,y]], y]},
 {"name":"division_r'",          "formula":[R, [g,[f,x,y],y], x]},
 {"name":"unary_commutative",    "formula":[R, [f,[h,x],[h,y]], [f,[h,y],[h,x]]]},
 {"name":"unary_involutive",     "formula":[R, [h,[f,x,y]], [f,[h,y],[h,x]]]},
 {"name":"interdistributive",    "formula":[R, [h,[f,x,y]], [g,[h,x],[h,y]]]},
 {"name":"unary_distributive",   "formula":[R, [h,[f,x,y]], [f,[h x],[h y]]]},
 {"name":"twisted_l",            "formula":[R, [[h,[f,x,y]],x], [f,x,[h,y]]]},
 {"name":"twisted_r",            "formula":[R, [x,[h,[f,y,x]]], [f,[h,y],x]]},
 {"name":"locality_l",           "formula":[R, [h,[f,[h,x],y]], [h,[f,x,y]]]},
 {"name":"locality_r",           "formula":[R, [h,[f,x,[h,y]]], [h,[f,x,y]]]},
 {"name":"unary_distributive_l", "formula":[R, [h[f,[h,x],y]], [f,[h,x],[h,y]]]},
 {"name":"unary_distributive_r", "formula":[R, [h[f,x,[h y]]], [f,[h x],[h y]]]},
 {"name":"absorbtive_l",         "formula":[R, [f,[h x],[h[x,y]]], [h,[f,x,y]]]},
 {"name":"absorbtive_r",         "formula":[R, [f,[h[x,y]],[h,y]], [h,[f,x,y]]]},
 {"name":"flexible",             "formula":[R, [f,[f,x,y],x], [f,x,[f,y,x]]]},
 
 {"name":"associative",          "formula":[R, [f,x,[f,y,z]], [f,[f,x,y],z]]},
 {"name":"commutative_l",        "formula":[R, [f,x,[f,y,z]], [f,y,[f,x,z]]]},
 {"name":"commutative_r",        "formula":[R, [f,[f,x,y],z], [f,[f,x,z],y]]},
 {"name":"interassociative_1",   "formula":[R, [f,x,[g,y,z]], [g,[f,x,y],z]]},
 {"name":"interassociative_2",   "formula":[R, [f,x,[g,y,z]], [f,[g,x,y],z]]},
 {"name":"distributive_l",       "formula":[R, [f,x,[g,y,z]], [g,[f,x,y],[f,x,z]]]},
 {"name":"distributive_r",       "formula":[R, [f,[g,x,y],z], [g,[f,x,z],[f,y,z]]]},
 {"name":"self_distributive_l",  "formula":[R, [f,x,[f,y,z]], [f,[f,x,y],[f,x,z]]]},
 {"name":"self_distributive_r",  "formula":[R, [f,[f,x,y],z], [f,[f,x,z],[f,y,z]]]},
 {"name":"central",              "formula":[R, [f,[f,x,y],[f,y,z]], y]},   // T. Evans: Am. Math. Monthly, April 1967, 362–372
 {"name":"directoid_absorption", "formula":[R, [f,x,[f,[f,x,y],z]], [f,[f,x,y],z]]},
 {"name":"directoid_absorbtion'","formula":[R, [f,[f,x,[f,y,z]],z], [f,x,[f,y,z]]]},
 {"name":"Moufang1",             "formula":[R, [f,[f,[f,x,y],x],z], [f,x,[f,y,[f,x,z]]]]},
 {"name":"Moufang2",             "formula":[R, [f,[f,[f,x,y],z],y], [f,x,[f,y,[f,z,y]]]]},
 {"name":"Moufang3",             "formula":[R, [f,[f,x,y],[f,z,x]], [f,[f,x,[f,y,z]],x]]},
 {"name":"Moufang4",             "formula":[R, [f,[f,x,y],[f,z,x]], [f,x,[f,[f,y,z],x]]]},
 
 {"name":"entropic",             "formula":[R, [f,[f,x,y],[f,z,w]], [f,[f,x,z],[f,y,w]]]},  // medial
 {"name":"paramedial",           "formula":[R, [f,[f,x,y],[f,z,w]], [f,[f,w,y],[f,z,x]]]},

 {"name":"complemented",         "formula":[And, [R, [f,x,[k,x]], 0], [R, 1, [g,x,[k,x]]]]},
 {"name":"order_preserving_u",   "formula":[Imp, [R,x,y], [R,[h,x],[h,y]]]},
 {"name":"order_reversing_u",    "formula":[Imp, [R,x,y], [R,[h,y],[h,x]]]},
 {"name":"cancelative_l",        "formula":[Imp, [R,[f,x,y],[f,x,z]], [R,y,z]]},
 {"name":"cancelative_r",        "formula":[Imp, [R,[f,x,y],[f,z,y]], [R,x,z]]},
 {"name":"naturally_ordered_l",  "formula":[Iff, [R,x,y], [Ex, z, [S,[f,z,x],y]]]},
 {"name":"naturally_ordered_r",  "formula":[Iff, [R,x,y], [Ex, z, [S,[f,x,z],y]]]},

 {"name":"transitive",           "formula":[Imp, [And,[R,x,y],[R,y,z]], [R,x,z]]},
 {"name":"order_preserving_l",   "formula":[Imp, [R,x,y], [R,[f,x,z],[f,y,z]]]},
 {"name":"order_preserving_r",   "formula":[Imp, [R,x,y], [R,[f,z,x],[f,z,y]]]},
 {"name":"order_reversing_l",    "formula":[Imp, [R,x,y], [R,[g,y,z],[g,x,z]]]},
 {"name":"order_reversing_r",    "formula":[Imp, [R,x,y], [R,[g,z,y],[g,z,x]]]},
 {"name":"join_r1",              "formula":[Imp, [R,x,y], [R,x,[g,y,z]]]},
 {"name":"join_r2",              "formula":[Imp, [R,x,z], [R,x,[g,y,z]]]},
 {"name":"meet_l1",              "formula":[Imp, [R,x,z], [R,[f,x,y],z]]},
 {"name":"meet_l2",              "formula":[Imp, [R,y,z], [R,[f,x,y],z]]},
 {"name":"join_l",               "formula":[Imp, [And,[R,x,z],[R,y,z]], [R,[g,x,y],z]]},
 {"name":"meet_r",               "formula":[Imp, [And,[R,x,y],[R,x,z]], [R,x,[f,y,z]]]},
 {"name":"residuated_l",         "formula":[Iff, [R,[f,x,y],z], [R,y,[g,x,z]]]},
 {"name":"residuated_r",         "formula":[Iff, [R,[f,x,y],z], [R,x,[g,z,y]]]}
]
