
/***************************************
										Let
***************************************/

/***************************************
										Sig
***************************************/
some sig Drone {
	position: one Intersection,
	commande: one Commande,
	//chemin : seq Receptacle
}

some sig Receptacle{
	position: one Intersection
}

one sig Entrepot{
	position: one Intersection,
	ensembleCommandes: set Commande
}

some sig Commande {
	destination: one Receptacle,
}

some sig Intersection {
	X : Int,
	Y : Int
}


/***************************************
										Fact
***************************************/

fact {
	all c:Commande | one d:Drone | d.commande = c //Chaque Drone a une commande, toutes les commandes ont un drone, une commande n'a pas plusieurs Drones
	all c:Commande | one e:Entrepot | c in e.ensembleCommandes //Les commandes sont dans l'entrepôt.
	all disj i1, i2: Intersection | i1.X != i2.X || i1.Y != i2.Y
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
	one Intersection
}

/***************************************
										Check
***************************************/

check unicity for exactly 5 Drone, exactly 5 Commande, exactly 6 Intersection, 1 Entrepot, 2 Receptacle
