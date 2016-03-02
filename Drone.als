open util/integer


/***************************************
										Sig
***************************************/


// 'some', pour qu'il y ai au moins un drone
some sig Drone {
	position: one Intersection,
	commande: lone Commande,
	DCAP: Int,
	Batterie: Int
}

some sig Receptacle {
	position: one Intersection,
	RCAP: Int
}

one sig Entrepot {
	position: one Intersection,
	ensembleCommandes: set Commande
}

sig EnsembleProduits {
	capacite: Int
}

some sig Commande {
	destination: one Receptacle,
	ensembleProd: lone EnsembleProduits //On permet de créer une commande pour aller à l'entrepôt, sans ensembleProd															  //pour gérer le retour .
}

sig Intersection {
	X : Int,
	Y : Int,
}


/***************************************
										Fact
***************************************/

fact {
	init //predicat d'initialisation

	all e:EnsembleProduits | some c:Commande | c.ensembleProd = e     // Ensemble de Produits appartient à une commande
	all c:Commande | some e:Entrepot | c in e.ensembleCommandes      // Les commandes sont dans l'entrepôt
	all e:EnsembleProduits | some dcap:Drone.DCAP | e.capacite <= dcap     // La capacité d'une commande est restreinte
	all c:Commande | one c.ensembleProd => c.destination.position != Entrepot.position     // Pas de commande livrée à l'entrepot

	//A améliorer
	all d:Drone | d.DCAP > 0 //implicite
	all r:Receptacle | r.RCAP > 0 //implicite
	all ep:EnsembleProduits | ep.capacite > 0 //implicite
	all d:Drone | d.Batterie >= 0 && d.Batterie <= 3 //batterie du drone
}

/* Il y a au moins un receptacle sur une intersection voisine de l'entrepot */
fact{
some r:Receptacle|
((r.position.X = Entrepot.position.X+1 || r.position.X = Entrepot.position.X-1) && (r.position.Y = Entrepot.position.Y))
||
((r.position.X = Entrepot.position.X)&& (r.position.Y = Entrepot.position.Y+1 || r.position.Y = Entrepot.position.Y-1))
}

/* Il n'existe pas 2 intersectiones identiques*/
fact IntersectionUnitaire {
	all i1: Intersection |all i2:Intersection|
	not (i1.X=i2.X && i1.Y=i2.Y)
}


//fact : restreindre commande avec ensembleProduit
//fact : capacité d'un receptacle ne doit pas être trop faible, capacite de l'ensemble pas trop importante


/***************************************
										Pred
***************************************/

pred init {
	all d:Drone | d.Batterie = 3
}
 
pred depotCmd {
	all d:Drone |
    (one d.commande  && d.commande.destination.position = d.position) =>
	no d.commande
}

pred JeVeuxAllerACeReceptacle[r1:Receptacle, objectifFinal:Receptacle] {
	distanceOk[r1, objectifFinal]||some r3 :Receptacle | distanceOk[r1,r3] && JeVeuxAllerACeReceptacle[r3,objectifFinal]&&r3!=r1
}

pred distanceOk[r1:Receptacle, r2:Receptacle]{
	abs[r1.position.X-r2.position.X] + abs[r1.position.Y-r2.position.Y] <=3
}

/***************************************
										Fun
***************************************/

fun abs[x: Int] : Int {
	(x<0) => (0-x) else (x)
}


/***************************************
										Run
***************************************/

run depotCmd for 1 Drone, 10 Intersection, 3 Receptacle, 3 Commande, 3 EnsembleProduits

/***************************************
										Assert
***************************************/



/***************************************
										Check
***************************************/


