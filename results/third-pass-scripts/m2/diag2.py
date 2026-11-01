from build import express, full_matrix_units
p=2
mats=full_matrix_units(p,2)
print("mats:", mats)
# E22 * E22 = E22 ; try to express it
E22 = mats[4]
print("express E22 ->", express(p, mats, E22))
print("express I ->", express(p, mats, mats[0]))
