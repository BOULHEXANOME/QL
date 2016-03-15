open util/integer
/***************************************
										Let
***************************************/

let DCAP = 5
let RCAP = 10


/***************************************
										Sig
	Se référer au modèle conceptuel des données
		pour plus d'informations sur les objets
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
	contenu: Int
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
	all d: Drone | d.commande.contenu <= DCAP && d.commande.contenu > 0
}

// les réceptacles ont une capacité max de RCAP
fact CapaciteReceptacle {
	all r: Receptacle | r.contenu <= RCAP
}

// Si la commande contient un ensemble de prod, alors elle ne peut pas être livrée à l'entrepôt
fact PasLivraisonEntrepot {
	all c:Commande | c.contenu > 0 => c.destination.position != Entrepot.position
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

// Un receptacle ne peut pas figurer dans sa propre liste des receptacles atteignables
fact ReceptacleNePeutPasAllerVersLuiMeme {
	all r:Receptacle | r not in r.listeRecep.elems
}

// Remplissage de la liste des receptacles accessibles par un receptacle
fact ListeReceptacleAuMoins1Accessible {
	all r1:Receptacle | some r2:Receptacle | 	r2 in elems[r1.listeRecep] && r1 in elems[r2.listeRecep]
}

// 
fact ListeReceptacleContraintesDistance{
	no r1:Receptacle | some r3:Receptacle | (distance[r1.position, r3.position] > 3 || distance[r1.position, r3.position]<=0) &&
	r3 in elems[r1.listeRecep]
}

// 
fact ListeReceptacleAjoutTousAccessibles{
	all r1:Receptacle | all r2:Receptacle | (distance[r1.position, r2.position] < 4 && distance[r1.position, r2.position]>0) =>
	(r2 in elems[r1.listeRecep] && r1 in elems[r2.listeRecep])
}

// Il n'y a pas deux fois le même receptacle dans la liste des receptacles atteignables
fact ListeReceptacleSansDoublons{
	all r1:Receptacle | ! hasDups[r1.listeRecep]
}

// Il doit exister un chemin tel qu'en partant d'un réceptacle, on puisse atteindre n'importe quel réceptacle de destination 
// en passant par une liste de réceptacles espacés de 3 ou moins les uns des autres
fact TousReceptaclesAccessibles{
	all r1,r2: Receptacle | some chemin: seq Receptacle | some r : Receptacle |
		/*last[chemin] != r && */last[chemin] = r1 && first[chemin] = r2  && r in chemin[idxOf[chemin,r]+1].listeRecep.elems =>
 		r in chemin.elems
}

// Chaque drone a un chemin qui ne comporte pas de doublons
fact CheminSansDoublons{
//	all d: Drone | ! hasDups[d.chemin]
	all d: Drone | # elems[d.chemin] = # inds[d.chemin]
}

// Les drones partent de l'entrepot
fact PremierDuChemin{
	all d:Drone | first[d.chemin]= Entrepot
}

// La deuxieme destination du Drone (après l'entrepot) est un receptacle situé à 3 ou moins de l'entrepot
fact SecondDuChemin{
	all d:Drone | some r: Receptacle | (distance[r.position, Entrepot.position] > 0 && distance[r.position, Entrepot.position] <= 3) => d.chemin[1]=r
}

// Le dernier receptacle que visitera un Drone est le receptacle de destination où il livrera sa commande
fact DernierDuChemin{
	all d:Drone | last[d.chemin]= d.commande.destination
}

// Il n'existe pas deux drones qui aient la même commande
fact CommandeUnSeulDrone{
	all disj d,d2:Drone | d.commande != d2.commande
}

// 
fact TestCheminPlusLong{
	all d: Drone | # inds[d.chemin] > 3
}

//
fact testSurCheminHS{
	all r : Receptacle| all d : Drone |
		/*last[d.chemin] != r && */
		r in d.chemin[idxOf[d.chemin,r]+1].listeRecep.elems
		=> r in d.chemin.elems
}

/***************************************
										Pred
***************************************/

// Sert à lancer la simulation
pred simuler {
	initialiser
}

// Etape d'initialisation qui regle les paramètres des Drones
pred initialiser {
	all d:Drone | d.batterie = 3
//	all d:Drone | calculerChemin[d]
}

/*pred calculerChemin[d:Drone] {
	all r : Receptacle |
		last[d.chemin] != r && 
		r in d.chemin[idxOf[d.chemin,r]+1].listeRecep.elems
		=> r in d.chemin.elems
		
}*/

/***************************************
										Fun
***************************************/

// Retourne la valeur absolue d'un entier
fun abs[x: Int] : Int {
	(x<0) => x.mul[-1] else (x)
}

// Calcule la distance de Manhattan entre deux intersections
fun distance[i1,i2: Intersection]: Int {
    abs[abs[i1.x.sub[i2.x]].add[abs[i1.y.sub[i2.y]]]]
}

/***************************************
										Run
***************************************/

// Execute le programme
run initialiser for exactly 1 Drone, exactly 6 Receptacle, 1 EnsembleProduits, exactly 1 Commande, 15 Intersection, 6 int, 17 PositionCible

/***************************************
										Assert
***************************************/



/***************************************
										Check
***************************************/


