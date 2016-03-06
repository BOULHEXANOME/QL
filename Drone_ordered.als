open util/integer
open util/ordering[Time]

/***************************************
										Sig
***************************************/

some sig Drone {
	Batterie:Int one -> Time
}

sig Time {}

/***************************************
										Fact
***************************************/

fact {
	all x : Drone | x.Batterie.first = 3

}


/***************************************
										Pred
***************************************/

pred moveDrone[t,t' : Time, d:Drone]{
	d.Batterie.t > 0 => d.Batterie.t' = d.Batterie.t.sub[1]
}

pred simul {
	all t:Time - last | let t' = t.next | { all d:Drone | moveDrone[t,t',d] }
}

/***************************************
										Fun
***************************************/

/***************************************
										Run
***************************************/

/***************************************
										Assert
***************************************/

assert fin{
	all d:Drone | some t:Time | d.Batterie.t = 0
}

/***************************************
										Check
***************************************/

run simul for exactly 2 Drone, 3 Time
