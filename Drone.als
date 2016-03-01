open util/integer
open DroneNSEO

sig Drone {
	position: one Intersection,
	commande: lone Commande,
	DCAP: Int
}

sig Receptacle {
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

sig Commande {
	destination: one Receptacle,
	ensembleProd: lone EnsembleProduits //On permet de créer une commande pour aller à l'entrepôt, sans ensembleProd
																  //pour gérer le retour .
}

assert restreindreCapacite {
	all e:EnsembleProduits | some dcap:Drone.DCAP | e.capacite <= dcap
}

fact {
	all e:EnsembleProduits | some c:Commande | c.ensembleProd = e
}

check restreindreCapacite for 1 Drone, 10 Intersection, 3 Receptacle, 3 Commande, 3 EnsembleProduits

//fact : restreindre commande avec ensembleProduit
//fact : capacité d'un receptacle ne doit pas être trop faible, capacite de l'ensemble pas trop importante

