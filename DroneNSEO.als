sig Intersection {
	id : one Int,
	intersectionN : one Intersection,
	intersectionS : one Intersection,
	intersectionE : one Intersection,
	intersectionO : one Intersection,
	}

fact IntersectionUnitaire {
	all i: Intersection | differentInter[i]
	}

pred differentInter[i : Intersection] {
	i != i.intersectionN 
	i != i.intersectionS 
	i != i.intersectionE 
	i != i.intersectionO 
	}

fact IntersectionReflective {
	all i1: Intersection | some i2,i3,i4,i5:Intersection |  reflexionInter[i1,i2,i3,i4,i5]
	}

pred reflexionInter[i1 : Intersection, i2  : Intersection, i3  : Intersection, i4  : Intersection, i5  : Intersection] {
	i1.intersectionN = i2
	i2.intersectionS = i1
	i1.intersectionE = i3
	i3.intersectionO = i1
	i4.intersectionN = i1
	i1.intersectionS = i4
	i5.intersectionE = i1
	i1.intersectionO = i5	
	}

fact NE {
	all i1: Intersection | some i2,i3,i4:Intersection |  NEpred[i1,i2,i3,i4]
	}
pred NEpred[i1 : Intersection, i2  : Intersection, i3  : Intersection, i4  : Intersection] {
	i1.intersectionN = i2
	i1.intersectionE = i3
	i2.intersectionE = i4
	i3.intersectionN = i4
}

fact NO {
	all i1: Intersection | some i2,i3,i4:Intersection |  NEpred[i1,i2,i3,i4]
	}
pred NOpred[i1 : Intersection, i2  : Intersection, i3  : Intersection, i4  : Intersection] {
	i1.intersectionN = i2
	i1.intersectionO = i3
	i2.intersectionO = i4
	i3.intersectionN = i4
}

fact SO {
	all i1: Intersection | some i2,i3,i4:Intersection |  NEpred[i1,i2,i3,i4]
	}
pred SOpred[i1 : Intersection, i2  : Intersection, i3  : Intersection, i4  : Intersection] {
	i1.intersectionS = i2
	i1.intersectionO = i3
	i2.intersectionO = i4
	i3.intersectionS = i4
}

fact SE {
	all i1: Intersection | some i2,i3,i4:Intersection |  NEpred[i1,i2,i3,i4]
	}
pred SEpred[i1 : Intersection, i2  : Intersection, i3  : Intersection, i4  : Intersection] {
	i1.intersectionS = i2
	i1.intersectionE = i3
	i2.intersectionE = i4
	i3.intersectionS = i4
	}
/*
fact UnSeul {
	all i1: Intersection | some i2,i3,i4,i5:Intersection |  UnSeulpred[i1,i2,i3,i4,i5]
	}
pred UnSeulpred [i1,i2,i3,i4,i5:Intersection] {
	i1.intersectionN = i2
	i1.intersectionS = i3
	i1.intersectionE = i4
	i1.intersectionO = i5
	i2!=i3
	i2!=i4
	i2!=i5
	i3!=i4
	i3!=i5
	i4!=i5
	}

fact IdIntersection {
	all i1: Intersection | some i2,i3,i4,i5:Intersection |  reflexionId[i1,i2,i3,i4,i5,3]
	}

pred reflexionId[i1 : Intersection, i2  : Intersection, i3  : Intersection, i4  : Intersection, i5 : Intersection, taille : Int] {
	i2.intersectionS.id = (i1.id)+taille
	i3.intersectionO.id = (i1.id)-1
	i4.intersectionN.id = (i1.id)-taille
	i5.intersectionE.id = (i1.id)+1
	}*/

assert Test1 {
	all i: Intersection | i != i.intersectionN && all i: Intersection | i != i.intersectionE
	}

assert Test2 {
	all i1: Intersection | some i2:Intersection | 	
	i1.intersectionN != i2 && i2.intersectionS = i1
	}
assert Test3 {
	all i1: Intersection | some i2:Intersection | 	
	i1.intersectionN = i2 && i2.intersectionS = i1
	}
check Test1 for 9 Intersection
check Test2 for 9 Intersection
check Test3 for 9 Intersection


