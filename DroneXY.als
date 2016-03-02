sig Intersection {
	X : Int,
	Y : Int,
}

fact{
some r:Receptacle|
((r.position.X = Entrepot.position.X+1 || r.position.X = Entrepot.position.X-1) && (r.position.Y = Entrepot.position.Y))
||
((r.position.X = Entrepot.position.X)&& (r.position.Y = Entrepot.position.Y+1 || r.position.Y = Entrepot.position.Y-1))
}

pred JeVeuxAllerACeReceptacle[r1:Receptacle, objectifFinal:Receptacle]{
	distanceOk[r1, objectifFinal]||some r3 :Receptacle | distanceOk[r1,r3] && JeVeuxAllerACeReceptacle[r3,objectifFinal]&&r3!=r1
}

pred distanceOk[r1:Receptacle, r2:Receptacle]{
abs(r1.position.X-r2.position.X)+abs(r1.position.Y-r2.position.Y)<=3
}

pred abs(x: Int, result: Int) {
x.lt[0] => 0.minus[x] && result.eq[0.minus[x]]
else x.gte[0] && result.eq[x] 
}



fact IntersectionUnitaire {
	all i1: Intersection |all i2:Intersection|
	not (i1.X=i2.X && i1.Y=i2.Y)
}/*
//Pour tout i, il existe un j tel que i = j
assert test1{all i1:Intersection | some i2:Intersection | i1.X=i2.X&&i1.Y=i2.Y}
//Il existe i, j tels que i!=j
assert test2{some i1:Intersection | some i2:Intersection | i1.X!=i2.X||i1.Y!=i2.Y}
check test1 for 7 Intersection
check test2 for 7 Intersection expect 7*/
