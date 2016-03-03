open util/integer

/***************************************
										Sig
***************************************/


// 'some', pour qu'il y ai au moins un drone
some sig Drone {
	position: one Intersection,
	commande: lone Commande,
	DCAP: Int,
	batterie: Int,
	chemin : one Chemin
}

one sig Temps{
tempsActuel:Int,

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
	ensembleProd: lone EnsembleProduits // On permet de créer une commande pour aller à l'entrepot, sans ensembleProd															  //pour gérer le retour .
}

sig Intersection {
	X : Int,
	Y : Int,
}

sig Chemin {
	listeReceptacles : seq Receptacle
}


/***************************************
										Fact
***************************************/

fact {
	initialiser // Predicat d'initialisation

	all e:EnsembleProduits | some c:Commande | c.ensembleProd = e     // Ensemble de Produits appartient à une commande
	all c:Commande | some e:Entrepot | c in e.ensembleCommandes      // Les commandes sont dans l'entrepôt
	all e:EnsembleProduits | some dcap:Drone.DCAP | e.capacite <= dcap     // La capacité d'une commande est restreinte
	all c:Commande | one c.ensembleProd => c.destination.position != Entrepot.position     // Pas de commande livrée à l'entrepot

	// A améliorer
	all d:Drone | d.DCAP > 0 // implicite
	all r:Receptacle | r.RCAP > 0 // implicite
	all ep:EnsembleProduits | ep.capacite > 0 // implicite
	all d:Drone | d.batterie >= 0 && d.batterie <= 3 // batterie du drone
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
	all disj i1,i2: Intersection |
	not (i1.X=i2.X && i1.Y=i2.Y)
}


//fact : restreindre commande avec ensembleProduit
//fact : capacité d'un receptacle ne doit pas être trop faible, capacite de l'ensemble pas trop importante


/***************************************
										Pred
***************************************/

pred simuler {
	initialiser
	iterer
}

pred initialiser {
	all d:Drone | d.batterie = 3
	Temps.tempsActuel = 0
	all d:Drone | attribuerCommande[d]
}

pred iterer {
	all d:Drone | allerAuReceptacle[d]
}

pred attribuerCommande[d:Drone] {
	some c:Commande | no d.commande => d.commande = c
}
 
pred deposerCmd {
	all d:Drone |
    (one d.commande  && d.commande.destination.position = d.position) =>
	no d.commande
}

pred allerACeReceptacle[d:Drone, r1:Receptacle, objectifFinal:Receptacle] {
	verifierDistance[r1, objectifFinal] 
	=> d.chemin.listeReceptacles = d.chemin.listeReceptacles.add[r1]
	else some r3 :Receptacle | (verifierDistance[r1,r3] && allerACeReceptacle[d,r3,objectifFinal] && r3 != r1) 
	=> d.chemin.listeReceptacles = d.chemin.listeReceptacles.add[r3] 
}

pred verifierDistance[r1:Receptacle, r2:Receptacle]{
	abs[r1.position.X-r2.position.X] + abs[r1.position.Y-r2.position.Y] <=3
}

pred allerAuReceptacle[d:Drone]{
	d.position.X<d.commande.destination.position.X => d.position.X=d.position.X+1
	else d.position.X>d.commande.destination.position.X => d.position.X=d.position.X-1
	else d.position.Y<d.commande.destination.position.Y => d.position.Y=d.position.Y+1
	else d.position.Y>d.commande.destination.position.Y => d.position.Y=d.position.X-1
	else allerAEntrepot[d]
}

pred allerAEntrepot[d:Drone]{
	d.position.X<Entrepot.position.X => d.position.X=d.position.X+1
	else d.position.X>Entrepot.position.X => d.position.X=d.position.X-1
	else d.position.Y<Entrepot.position.Y => d.position.Y=d.position.Y+1
	else d.position.Y>Entrepot.position.Y => d.position.Y=d.position.X-1
	else attribuerCommande[d]
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

run simuler for 3 Drone, 5 Intersection, 3 Receptacle, 3 Commande, 3 EnsembleProduits, 1 Chemin


/***************************************
										Assert
***************************************/

assert Test1 {
	some x : Int |  abs[x]<0
	}

/***************************************
										Check
***************************************/

check Test1 for 3
