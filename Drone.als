open util/integer
open DroneXY


//some, pour qu'il y en ai au moins un
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

pred init {
	all d:Drone | d.Batterie = 3
}
 
pred depotCmd {
	all d:Drone |
    (one d.commande  && d.commande.destination.position = d.position) =>
	no d.commande
}

fact {
	init //predicat d'initialisation

	all e:EnsembleProduits | some c:Commande | c.ensembleProd = e //ensemble de Produit appartient à une commande
	all c:Commande | some e:Entrepot | c in e.ensembleCommandes //Les commandes sont dans l'entrepôt
	all e:EnsembleProduits | some dcap:Drone.DCAP | e.capacite <= dcap //La capacité d'une commande est restreinte
	all c:Commande | one c.ensembleProd => c.destination.position != Entrepot.position //Pas de commande livrée à l'entrepot

	//A améliorer
	all d:Drone | d.DCAP > 0 //implicite
	all r:Receptacle | r.RCAP > 0 //implicite
	all ep:EnsembleProduits | ep.capacite > 0 //implicite
	all d:Drone | d.Batterie >= 0 && d.Batterie <= 3 //batterie du drone
}

run depotCmd for 1 Drone, 10 Intersection, 3 Receptacle, 3 Commande, 3 EnsembleProduits

//fact : restreindre commande avec ensembleProduit
//fact : capacité d'un receptacle ne doit pas être trop faible, capacite de l'ensemble pas trop importante

