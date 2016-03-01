sig Intersection {
	X : Int,
	Y : Int,
}


fact IntersectionUnitaire {
	all i1: Intersection |all i2:Intersection| different[i1,i2]
	}

pred different[i1 : Intersection, i2  : Intersection]{
	(i1.X=i2.X && i1.Y=i2.Y)
	}
//Pour tout i, il existe un j tel que i = j
assert test1{all i1:Intersection | some i2:Intersection | i1.X=i2.X&&i1.Y=i2.Y}
//Il existe i, j tels que i!=j
assert test2{some i1:Intersection | some i2:Intersection | i1.X!=i2.X||i1.Y!=i2.Y}
check test1 for 7 Intersection
check test2 for 7 Intersection expect 7
