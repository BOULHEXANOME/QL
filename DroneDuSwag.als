open util/integer
/***************************************
										Let
***************************************/

let DCAP = 5
let RCAP = 10


/***************************************
										Sig
***************************************/

some sig Drone {
	position: one Intersection,
	commande: lone Commande,
	batterie: Int,
	chemin : seq PositionCible
}

one sig Temps {
	tempsActuel:Int
}

abstract sig PositionCible{
	listeRecep : seq Receptacle,
	position: one Intersection
}

some sig Receptacle extends PositionCible{
	contenu : Int
}

one sig Entrepot extends PositionCible{
	ensembleCommandes: set Commande
}

sig EnsembleProduits {
	contenu: Int
}

some sig Commande {
	destination: one PositionCible,
	ensembleProd: lone EnsembleProduits // On permet de créer une commande pour aller à l'entrepot, sans ensembleProd pour gérer le retour du drone
}

sig Intersection {
	x : Int,
	y : Int
}


/***************************************
										Fact
***************************************/

// la batterie du drone est entre 0 et 3
fact BatterieDrone {
	all d:Drone | d.batterie >= 0 && d.batterie <= 3
}

// les drones ont une capacité max de DCAP
fact CapaciteDrone {
	all d: Drone | d.commande.ensembleProd.contenu <= DCAP && d.commande.ensembleProd.contenu > 0
}

// les réceptacles ont une capacité max de RCAP
fact CapaciteReceptacle {
	all r: Receptacle | r.contenu <= RCAP
}


// Ensemble de Produits appartient à une commande
fact EnsembleProdDansCommande {
	all e:EnsembleProduits | some c:Commande | c.ensembleProd = e
}

// L'entrepôt a une liste de toutes les commandes
fact EntrepotListeCommande {
	all c:Commande | some e:Entrepot | c in e.ensembleCommandes
}

// Si la commande contient un ensemble de prod, alors elle ne peut pas être livrée à l'entrepôt
fact PasLivraisonEntrepot {
	all c:Commande | one c.ensembleProd => c.destination.position != Entrepot.position
}

// Il y a au moins un receptacle sur une intersection voisine de l'entrepot
fact EntrepotAUnVoisin {
	some r:Receptacle | distance[r.position, Entrepot.position] = 1
}


// Il n'existe pas 2 intersectiones identiques
fact IntersectionUnitaire {
	all disj i1,i2: Intersection | i1.x != i2.x || i1.y != i2.y
}

// Il n'existe pas des intersections avec 2 receptacles
fact ReceptacleUnitaire {
	all disj r1,r2: Receptacle |
	not (r1.position=r2.position)
}

// aucun réceptacle ne peut partager son intersection avec l'entrepôt
fact EntrepotPasSurReceptacle {
	all r: Receptacle | not (Entrepot.position = r.position)
}

// taille de la grille
fact LimitationPositions {
	all i:Intersection | i.x <=5 && i.x >= -5 && i.y <=5 && i.y >=-5
}

fact ReceptacleNePeutPasAllerVersLuiMeme {
	all r:Receptacle | r not in r.listeRecep.elems
}


// Remplissage liste des receptacles accessibles
fact ListeReceptacleAuMoins1Accessible {
	all r1:Receptacle | some r2:Receptacle | r2 in elems[r1.listeRecep] && r1 in elems[r2.listeRecep]
}
fact ListeReceptacleContraintesDistance{
	no r1:Receptacle | some r3:Receptacle | (distance[r1.position, r3.position] > 3 || distance[r1.position, r3.position]<=0) &&
	r3 in elems[r1.listeRecep]
}
fact ListeReceptacleAjoutTousAccessibles{
	all r1:Receptacle | all r2:Receptacle | (distance[r1.position, r2.position] < 4 && distance[r1.position, r2.position]>0) =>
	(r2 in elems[r1.listeRecep] && r1 in elems[r2.listeRecep])
}
fact ListeReceptacleSansDoublons{
	all r1:Receptacle | ! hasDups[r1.listeRecep]
}

fact TousReceptaclesAccessibles{
	all r1,r2 : Receptacle | some chemin : seq Receptacle | no r3 : Receptacle | 
		r2 != r3 && last[chemin] = r2 && first[chemin] = r1  && r3 in chemin.elems && r3  !in chemin[idxOf[chemin,r3]+1].listeRecep.elems
}

fact CheminSansDoublons{
	all d: Drone | # elems[d.chemin] = # inds[d.chemin]
}
fact PremierDuChemin{
	all d:Drone | first[d.chemin]= Entrepot
}
fact SecondDuChemin{
	all d:Drone | some r: Receptacle | (distance[r.position, Entrepot.position] > 0 && distance[r.position, Entrepot.position] <= 3) => d.chemin[1]=r
}
fact DernierDuChemin{
	all d:Drone | last[d.chemin]= d.commande.destination
}
fact CommandeUnSeulDrone{
	all disj d,d2:Drone | d.commande != d2.commande
}
fact testSurCheminHS{
	all d : Drone | no r1 : Receptacle | 
		 last[d.chemin] != r1 && r1 in d.chemin.elems && r1  !in d.chemin[idxOf[d.chemin,r1]+1].listeRecep.elems
}

/***************************************
										Pred
***************************************/

pred simuler {
	initialiser
}

pred initialiser {
	all d:Drone | d.batterie = 3
	//all d:Drone | calculerChemin[d]
}
/*
pred calculerChemin[d:Drone] {
	all r : Receptacle |
		last[d.chemin] != r && 
		r in d.chemin[idxOf[d.chemin,r]+1].listeRecep.elems
		<=> r in d.chemin.elems
		
}*/

/***************************************
										Fun
***************************************/

// calcule la valeur absolue
fun abs[x: Int] : Int {
	(x<0) => x.mul[-1] else (x)
}

// calcule la distance entre deux intersections
fun distance[i1,i2: Intersection]: Int {
    abs[abs[i1.x.sub[i2.x]].add[abs[i1.y.sub[i2.y]]]]
}

/***************************************
										Run
***************************************/

run initialiser for exactly 1 Drone, exactly 6 Receptacle, 1 EnsembleProduits, exactly 1 Commande, 15 Intersection, 6 int, 17 PositionCible

/***************************************
										Assert
***************************************/



/***************************************
										Check
***************************************/


