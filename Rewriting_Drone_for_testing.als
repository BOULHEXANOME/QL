open util/integer

/***************************************
										Let
***************************************/

/***************************************
										Sig
***************************************/
some sig Drone {
	//position: one Intersection,
	commande: one Commande,
	//chemin : seq Receptacle
}

/*some sig Receptacle{
	position: one Intersection
}*/

one sig Entrepot{
	//position: one Intersection,
	ensembleCommandes: set Commande
}

some sig Commande {
	//destination: one Receptacle,
}

/*sig Intersection {
	X : Int,
	Y : Int,
}*/


/***************************************
										Fact
***************************************/

fact {
	all d:Drone | one c:Commande | d.commande = c
	all d:Drone | no d':Drone | d.commande = d'.commande
}


/***************************************
										Pred
***************************************/


/***************************************
										Run
***************************************/

//run initialiser for exactly 5 Drone, exactly 5 Commande

/***************************************
										Assert
***************************************/

assert unicity {
	no c:Commande | some d:Drone | d.commande = c
}

/***************************************
										Check
***************************************/

check unicity for 5
