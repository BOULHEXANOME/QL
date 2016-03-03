open util/integer
open util/ordering[State]

/***************************************
										Sig
***************************************/

some sig Drone {
	Batterie:Int
}

sig State {charged, done : set Drone}

/***************************************
										Fact
***************************************/

fact {first.charged = Drone && no first.done
		all x : first.charged | x.Batterie = 0}

fact {
	all s: State, s' : s.next{
		moveDrone[s.charged, s'.charged, s.done, s'.done]
	}
}

/***************************************
										Pred
***************************************/

pred moveDrone[from, from', to, to': set Drone]{
	all x: from | {
		x.Batterie.pos => {from' = from + x.reduceBatterie
										to' = to} 
		x.Batterie = 0 => {from' = from - x
									   to' = to + x }
	}
}

/***************************************
										Fun
***************************************/

fun reduceBatterie[x:Drone] : Drone{
	{y : Drone | y.Batterie=x.Batterie.sub[1]}
}

/***************************************
										Run
***************************************/
run {last.done = Drone}

/***************************************
										Assert
***************************************/

/***************************************
										Check
***************************************/
