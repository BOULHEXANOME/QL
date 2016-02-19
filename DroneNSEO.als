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

assert Test1 {
	all i: Intersection | i != i.intersectionN && all i: Intersection | i != i.intersectionE
	}

assert Test2 {
	all i1: Intersection | some i2:Intersection | 	
	i1.intersectionN != i2 && i2.intersectionS = i1
	}

check Test2 for 3 Intersection
