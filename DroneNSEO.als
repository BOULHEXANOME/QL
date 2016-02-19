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
	all i1: Intersection | some i2:Intersection |  reflexionInter[i1,i2]
	}

pred reflexionInter[i1 : Intersection, i2  : Intersection] {
	i1.intersectionN = i2
	i2.intersectionS = i1
	i1.intersectionE = i2
	i2.intersectionO = i1

	
	}


assert Test1 {
	all i: Intersection | i != i.intersectionN && all i: Intersection | i != i.intersectionE
	}

assert Test2 {
	all i1: Intersection | some i2:Intersection | 	
	i1.intersectionN != i2 && i2.intersectionS = i1
	}

check Test2 for 3 Intersection
