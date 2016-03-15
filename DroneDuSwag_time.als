/***************************************
Cette version permet de gérer la position des Drones dans le temps, à l'aide de la bibliothèque util/ordering
appliqué au Temps.
De cette façon, nous introduisons le temps comme une succession d'états, allant de first à last, où chaque état
est défini par rapport à son précédent. L'idée est donc de considérer les attributs de nos signatures comme
dépendants du temps, ce qui permet de simuler l'avancée des drones selon le chemin précalculé.
De cette façon, nous pouvons gérer le comportement de la batterie en ce qui concerne la batterie, le chargement
et déchargement de commande, et les collisions.

FONCTIONNALITES : (SANS CHEMIN DISPONIBLE, DONC PAS TESTE !!)
	- Déplacement des drones de réceptacles en réceptacles
	- Batterie
	- Chargement d'une commande
	- Déchargement d'une commande

TODO :
	- Réparer le calcul du chemin
	- Déplacement avec intersections
	- Gestion des collisions

***************************************/
open util/integer
open util/ordering[Temps]
/***************************************
										Let
***************************************/

let DCAP = 5
let RCAP = 10

/***************************************
										Sig

Les signatures sont les mêmes qu'auparavant, cependant, nous faisons dépendre certains attributs du temps, afin de
les rendres modifiables au fur et à mesure de l'avancement des états.
***************************************/


some sig Drone {
	position: Intersection one -> Temps,
	commande: one Commande,
	batterie: Int one->Temps,
	chemin : seq Receptacle->Temps
}

sig Temps {}

abstract sig PositionCible{
	listeRecep : seq Receptacle,
	position: one Intersection
}

some sig Receptacle extends PositionCible{
	contenu : Int one->Temps
}

one sig Entrepot extends PositionCible{
	ensembleCommandes: set Commande -> Temps
}


some sig Commande {
	destination: PositionCible one -> Temps,
	contenu: Int one->Temps
}

sig Intersection {
	X : Int,
	Y : Int
}

/***************************************
										Fact

Les faits sont les mêmes que pour la première partie, à ceci près qu'ils sont réfactorés pour fonctionner
avec l'introduction des états temporels.
***************************************/

// la batterie du drone est entre 0 et 3
fact BatterieDrone {
	all d:Drone, t:Temps | d.batterie.t >= 0 && d.batterie.t < 4
}

// les drones ont une capacité max de DCAP
fact CapaciteDrone {
	all c:Commande, t:Temps | c.contenu.t<= DCAP && c.contenu.t>= 0
}

// les réceptacles ont une capacité max de RCAP
fact CapaciteReceptacle {
	all r: Receptacle, t:Temps | r.contenu.t <= RCAP && r.contenu.t >= 0
}

// Si la commande a un contenu positif, alors elle ne peut pas être livrée à l'entrepôt
fact PasLivraisonEntrepot {
	all c:Commande, t:Temps | c.contenu.t > 0 => c.destination.t != Entrepot
}

// Il y a au moins un receptacle sur une intersection voisine de l'entrepot
fact EntrepotAUnVoisin {
	some r:Receptacle | distance[r.position, Entrepot.position] = 1
}

// Il n'existe pas 2 intersectiones identiques
fact IntersectionUnitaire {
	all disj i1,i2: Intersection | i1.X != i2.X || i1.Y != i2.Y
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
	all i:Intersection | i.X <=5 && i.X >= 0 && i.Y <= 5 && i.Y >= 0
}

// Un receptacle ne peut pas figurer dans sa propre liste des receptacles atteignables
fact ReceptacleNePeutPasAllerVersLuiMeme {
	all r:Receptacle | r not in r.listeRecep.elems
}

// Remplissage liste des receptacles accessibles
fact ListeReceptacleAuMoins1Accessible {
	all r1:Receptacle | some r2:Receptacle | 	r2 in elems[r1.listeRecep] && r1 in elems[r2.listeRecep]
}

//Les réceptacles appartenant à la liste des réceptacles d'un autre accessibles sont distant de 3 ou moins avec ce dernier
fact ListeReceptacleContraintesDistance{
	no r1:Receptacle | some r3:Receptacle | (distance[r1.position, r3.position] > 3 || distance[r1.position, r3.position]<=0) &&
	r3 in elems[r1.listeRecep]
}

//Tous les réceptacles accessibles appartiennent à la liste des réceptacles d'au moins un autre.
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
	all d: Drone, t:Temps | # elems[d.chemin.t] = # inds[d.chemin.t]
}

// Les drones partent de l'entrepot
fact PremierDuChemin{
	all d:Drone, t:Temps | some r: Receptacle | !d.chemin.t.isEmpty => (first[d.chemin.t]= r && distance[Entrepot.position, r.position] <= 3)
}

// La deuxieme destination du Drone (après l'entrepot) est un receptacle situé à 3 ou moins de l'entrepot
fact SecondDuChemin{
	all d:Drone, t:Temps | some r: Receptacle | !d.chemin.t.isEmpty => ((distance[r.position, Entrepot.position] > 0 && distance[r.position, Entrepot.position] <= 3) => d.chemin.t[1]=r)
}

// Le dernier receptacle que visitera un Drone est le receptacle de destination où il livrera sa commande
fact DernierDuChemin{
	all d:Drone, t:Temps | !d.chemin.t.isEmpty => (last[d.chemin.t]= d.commande.destination.t)
} 

// Il n'existe pas deux drones qui aient la même commande
fact CommandeUnSeulDrone{
	all disj d,d2:Drone, t:Temps | let c = d.commande | (c.destination.t != Entrepot &&c.contenu.t != 0)=>d.commande != d2.commande
}

//Ce fait permet d'imposer l'univers pour que les prédicats de contrôle soient vérifiés en permanence.
fact {go}


/***************************************
										Pred

Les prédicats servent de points de contrôles pour les états : Ils vont gérer la transition des attributs
dépendants du temps entre les états temporels, en fonction de la situation actuelle du drone.
Le fonctionnement détaillé est expliqué dans le rapport.

***************************************/

//Prédicat racine du programme, à lancer avec run pour effectuer la simulation.
pred go {
	initialiser
	all t:Temps - last |let t'=t.next |
	{
		all d:Drone | bougerDrone[t,t',d]
		/*all c:Commande | c in Entrepot.ensembleCommandes.t => c.contenu.t'=c.contenu.t && c.destination.t'=c.destination.t
		Entrepot.ensembleCommandes.t'=Entrepot.ensembleCommandes.t*/
	}
}

//Prédicat d'initialisation : Il permet de définir les attributs initiaux pour l'état temporel first.
pred initialiser {
	all d:Drone | {
		d.batterie.first = 3
		d.position.first = Entrepot.position
		d.commande.contenu.first = 0
		d.commande.destination.first = Entrepot
		d.chemin.first.isEmpty
	}
	all d:Drone, c:Commande | c.contenu.first = 0 => d.commande = c
	all c:Commande | c.contenu.first > 0 => c in Entrepot.ensembleCommandes.first
	all r:Receptacle | r.contenu.first = 0
}

//Prédicat de calcul du chemin : PAS A JOUR, ET PAS FONCTIONNEL
pred calculerChemin[d:Drone, t:Temps] {
	all r : Receptacle |
		/*last[d.chemin] != r && */
		r in d.chemin.t[idxOf[d.chemin.t,r]+1].listeRecep.elems
		=> r in d.chemin.t.elems
}


//Prédicat gérant le mouvement du Drone, en fonction de la situation
pred bougerDrone[t,t':Temps, d:Drone]{
	
	// la commande du drone est vide et le drone et à l'entrepot et il reste des commandes à livrer non vide
	some c:Commande | (c in Entrepot.ensembleCommandes.t && c.contenu.t > 0 && d.commande.contenu.t = 0 && d.position.t = Entrepot.position)
		=> (d.commande.destination.t' = c.destination.t && d.commande.contenu.t' = c.contenu.t)
	
	//Le drone contient une commande, il est en chemin : il doit se déplacer
	d.commande.contenu.t !=0 && d.position.t != d.commande.destination.t.position => deplacerDrone[d,t,t']

	//Le drone contient une commande, il est à destination : il doit décharger
	d.commande.contenu.t!=0 && d.position.t = d.commande.destination.t.position => dechargementCommande[d,t,t']
}

//Prédicat gérant le déplacement du drone 
pred deplacerDrone[d:Drone,t,t':Temps]{
	
	d.commande.contenu.t > 0 =>{//Le drone a la commande chargée
	//Le drone a assez de batterie
	d.batterie.t >= d.position.t.distance[d.chemin.t[d.chemin.t.idxOf[d.position.t]+1].position] =>{
		d.position.t' = d.chemin.t[d.chemin.t.idxOf[d.position.t]+1].position
		d.batterie.t'=d.batterie.t.sub[1]
	}else{//Le drone doit recharger
		d.position.t' = d.position.t
		d.batterie.t' = d.batterie.t.add[1]
	}
	}else{//le drone est en retour à l'entrepôt
	//le drone a assez de batterie
	d.batterie.t >= d.position.t.distance[d.chemin.t[d.chemin.t.idxOf[d.position.t]-1].position] =>{
		d.position.t' = d.chemin.t[d.chemin.t.idxOf[d.position.t]-1].position
		d.batterie.t'=d.batterie.t.sub[1]
	}else{//Le drone doit recharger
		d.position.t' = d.position.t
		d.batterie.t' = d.batterie.t.add[1]
	}
	}

	d.chemin.t' = d.chemin.t
	d.commande.destination.t' = d.commande.destination.t
	d.commande.contenu.t' = d.commande.contenu.t
	all r:Receptacle | r.contenu.t' = r.contenu.t
}

//Prédicat gérant le déchargement de la commande
pred dechargementCommande[d:Drone, t,t':Temps]{
	d.position.t' = d.position.t
	d.batterie.t' = d.batterie.t
	d.chemin.t'=d.chemin.t	
	d.commande.destination.t.contenu.t'=d.commande.destination.t.contenu.t.add[d.commande.contenu.t]
	d.commande.contenu.t' = 0
	d.commande.destination.t' = d.commande.destination.t
	all r:Receptacle-d.commande.destination.t | r.contenu.t' = r.contenu.t
}	

/***************************************
										Fun
***************************************/

// calcule la valeur absolue
fun abs[x: Int] : Int {
	(x<0) => x.mul[-1] else (x)
}

// calcule la distance entre deux intersections
fun distance[i1,i2: Intersection]: Int {
    abs[abs[i1.X.sub[i2.X]].add[abs[i1.Y.sub[i2.Y]]]]
}

/***************************************
										Run
***************************************/

run go for 1 Drone, exactly 2 Receptacle, exactly 2 Commande,  6 Intersection, 7 int, exactly 5 Temps

/***************************************
										Assert
***************************************/

//Assertion de fin : si cette dernière est vérifiée, alors il existe un temps où l'on retrouve la situation dite finale :
// - Tous les Drones sont à l'entrepôts
// - Toutes les drones sont déchargées
// - La liste de commandes de l'entrepôt est vide
assert fin {
	some t:Temps |{
		all d:Drone, c:Commande | {
			d.position.t = Entrepot.position
			c.contenu.t = 0
		}
		no c:Commande | c in Entrepot.ensembleCommandes.t
	}
}


/***************************************
										Check
***************************************/

check fin
