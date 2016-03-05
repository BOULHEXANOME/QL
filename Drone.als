open util/integer

/***************************************
										Let
***************************************/

let DCAP = 5
let RCAP = 10


/***************************************
										Sig
***************************************/


// 'some', pour qu'il y ait au moins un drone
some sig Drone {
	position: one Intersection,
	commande: lone Commande,
	batterie: Int,
//	chemin : seq Receptacle
	chemin : one Chemin
}

one sig Temps {
	tempsActuel:Int
}

some sig Receptacle {
	position: one Intersection,
	next: lone Receptacle,
	contenu : Int
}


sig Chemin {
	actuel: one Receptacle,
	suivant: lone Chemin
}

one sig Entrepot {
	position: one Intersection,
	ensembleCommandes: set Commande
}

sig EnsembleProduits {
	contenu: Int
}

some sig Commande {
	destination: one Receptacle,
	ensembleProd: lone EnsembleProduits // On permet de créer une commande pour aller à l'entrepot, sans ensembleProd pour gérer le retour du drone
}

sig Intersection {
	X : Int,
	Y : Int,
}

/***************************************
										Fact
***************************************/

fact {
	all e:EnsembleProduits | some c:Commande | c.ensembleProd = e     // Ensemble de Produits appartient à une commande
	all c:Commande | some e:Entrepot | c in e.ensembleCommandes      // Les commandes sont dans l'entrepôt. ça sert à rien ça non ?
	all c:Commande | one c.ensembleProd => c.destination.position != Entrepot.position     // Pas de commande livrée à l'entrepot si la commande contient un ensembleProd

	// A améliorer
	all ep:EnsembleProduits | ep.contenu> 0 // implicite
	
}

// la batterie du drone est entre 0 et 3
fact BatterieDrone {
	all d:Drone | d.batterie >= 0 && d.batterie <= 3
}

// les drones ont une capacité max de DCAP
fact CapaciteDrone {
	all d: Drone | d.commande.ensembleProd.contenu <= DCAP
}

// les réceptacles ont une capacité max de RCAP
fact CapaciteReceptacle {
	all r: Receptacle | r.contenu <= RCAP
}

/* Il y a au moins un receptacle sur une intersection voisine de l'entrepot */
fact EntrepotAUnVoisin {
	some r:Receptacle | 
	((r.position.X = Entrepot.position.X+1 || r.position.X = Entrepot.position.X-1) && (r.position.Y = Entrepot.position.Y))
	||
	((r.position.X = Entrepot.position.X) && (r.position.Y = Entrepot.position.Y+1 || r.position.Y = Entrepot.position.Y-1))
}

/* Il n'existe pas 2 intersectiones identiques*/
fact IntersectionUnitaire {
	all disj i1,i2: Intersection | i1 != i2
}

/* Il n'existe pas des intersections avec 2 receptacles */
fact ReceptacleUnitaire {
	all disj r1,r2: Receptacle |
	not (r1.position=r2.position)
}

/* aucun réceptacle ne peut partager son intersection avec l'entrepôt */
fact EntrepotPasSurReceptacle {
	all r: Receptacle | not (Entrepot.position = r.position)
}


/* le chemin ne peut pas passer deux fois par la même intersection */
/*fact CheminPasDeDoublon {
	all d: Drone | not d.chemin.hasDups
}*/


/*
	//essai raté pour lier les receptacle N°1 et N°2
fact ReceptaclesVoisins {
	some chemin: seq Receptacle | all n: Int | n > -1 && n < #chemin => distance[chemin[n].position,chemin[n+1].position] < 4
	some chemin: seq Receptacle | all r:Receptacle |  all n: Int | r in elems[chemin] && n > -1 && n < #chemin && distance[chemin[n].position,chemin[n+1].position] < 4
	//all r1:Receptacle | all r2:Receptacle | testerChemin[r1, r2] 
}

	//essai raté pour lier les receptacle N°3
fact TousLesReceptaclesSontLies{
	all r1,r2:Receptacle | some chemin:seq Receptacle | r1 in chemin.elems && r2 in chemin.elems && r1!=r2
}
*/

	//essai pour lier les receptacle N°4
/*
// le suivant d'un réceptacle ne peut être lui-même
fact SuivantNonReflexif {
	no r:Receptacle | r = r.next
}

// tous les réceptacles de la carte sont quelque part dans le chemin
fact ToutReceptacleDansChemin {
	all r:Receptacle | r in Chemin.root.*next 
}

// un même réceptacle n'apparaît pas deux fois dans le chemin
fact SuivantPasCyclique {
	no r:Receptacle | r in r.^next 
}

// la distance entre un réceptacle et son suivant est forcément inférieure ou égale à 3
fact VerificationDistance {
	all r:Receptacle | distance[r.position,r.next.position]<4 
}*/

// taille de la grille
fact LimitationPositions {
	all i:Intersection | i.X <=10 && i.X >= -10 && i.Y <= 10 && i.Y >= -10
}


	// DERNIER TENTATIVE FAITS SUR LE CHEMIN
// il n'y a pas deux chemins identiques
fact CheminUnique {
	all disj c1, c2: Chemin | c1.actuel != c2.actuel || c1.suivant != c2.suivant
}

// il y a une distance de 3 max entre chaque réceptacle
fact VerifierDistance {
	all c:Chemin | one c.suivant => distance[c.actuel.position, c.suivant.actuel.position] <= 3
}

// il y a toujours un chemin entre deux réceptacles
fact ToujoursChemin {
	all r1, r2: Receptacle |
		r1 != r2 => (some ch:Chemin | calculerCheminBis[r1, r2, ch])
}

// le chemin ne boucle pas sur lui-même
fact SuivantNonCyclique {
	all c: Chemin | c.actuel not in c.^suivant.actuel
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
	Temps.tempsActuel = 0
	all d:Drone | d.batterie = 3
	all d:Drone | attribuerCommande[d]
	all d:Drone | trouverPremierReceptacle[d]
//	all d:Drone | calculerChemin[d, first[d.chemin], d.commande.destination]
	all d:Drone | some c:Chemin | calculerCheminBis[d.chemin.actuel, d.commande.destination, c]
}

pred iterer {
	all d:Drone | allerAuReceptacle[d]
}


pred attribuerCommande[d:Drone] {
	one c:Commande | no d.commande => d.commande = c // one Commande ou some ?
}
 
pred deposerCmd {
	all d:Drone |
    (one d.commande  && d.commande.destination.position = d.position) =>
	no d.commande
}

// permet de trouver le prochain plus proche réceptacle pour remplir la liste (récursif, ne fonctionne pas)
/*pred calculerChemin[d:Drone, r1:Receptacle, objectifFinal:Receptacle] {
	verifierDistanceRecep[r1, objectifFinal] 
	=> d.chemin.listeReceptacles = d.chemin.listeReceptacles.add[r1]
	else some r3 :Receptacle | (verifierDistanceRecep[r1,r3] && calculerChemin[d,r3,objectifFinal] && r3 != r1) 
	=> d.chemin.listeReceptacles = d.chemin.listeReceptacles.add[r3] 
}*/

// calcul du chemin avec notre technique
/*pred calculerChemin[d:Drone, r1:Receptacle, objectifFinal:Receptacle] {
	some liste:seq Receptacle |
	(first[liste] = r1 && last[liste] = objectifFinal &&
	(all r:Receptacle | r in liste.elems && 
	((verifierDistanceRecep[liste[liste.idxOf[r]], liste[liste.idxOf[r]+1]] || r=last[liste]))
	&&(verifierDistanceRecep[liste[liste.idxOf[r]], liste[liste.idxOf[r]-1]] || r=first[liste])))
	=> d.chemin= liste
}*/

// calcul du chemin avec le chemin chaîné
pred calculerCheminBis[debut, fin: Receptacle, cheminDeb: Chemin] {
	one cheminFin: Chemin |
	cheminDeb.actuel = debut // le chemin commence par le premier réceptacle
	&& cheminFin.actuel = fin // et termine par le dernier
	&& no cheminFin.suivant // le dernier chemin n'a pas de suivant
	&& cheminFin in cheminDeb.^suivant // le dernier chemin fait partie des suivants du premier (fermeture transitive)
}


// inutilisé
/*
pred testerChemin[r1:Receptacle, objectifFinal:Receptacle] {
	some liste:seq Receptacle |
	(first[liste] = r1 && last[liste] = objectifFinal &&
	(all r:Receptacle | r in liste.elems && 
	((verifierDistanceRecep[liste[liste.idxOf[r]], liste[liste.idxOf[r]+1]] || r=last[liste]))
	&&(verifierDistanceRecep[liste[liste.idxOf[r]], liste[liste.idxOf[r]-1]] || r=first[liste])))
}*/


pred trouverPremierReceptacle[d:Drone] {
	some r:Receptacle |	
	verifierDistanceInter[d.position, r.position] 
//	=> d.chemin= d.chemin.add[r]
	=> d.chemin.actuel = r
}

pred verifierDistanceRecep[r1:Receptacle, r2:Receptacle]{
	distance[r1.position, r2.position] < 4
}

pred verifierDistanceInter[i1:Intersection, i2:Intersection]{
	abs[i1.X-i2.X] + abs[i1.Y-i2.Y] < 4
}

// à modifier : il ne va plus à sa destination finale mais au suivant de sa liste de réceptacles
pred allerAuReceptacle[d:Drone]{
	d.position.X<d.commande.destination.position.X => d.position.X=d.position.X+1
	else d.position.X>d.commande.destination.position.X => d.position.X=d.position.X-1
	else d.position.Y<d.commande.destination.position.Y => d.position.Y=d.position.Y+1
	else d.position.Y>d.commande.destination.position.Y => d.position.Y=d.position.X-1
	else allerAEntrepot[d]
}

// idem
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

// calcule la valeur absolue
fun abs[x: Int] : Int {
	(x<0) => x.mul[-1] else (x)
}

// calcule la distance entre deux intersections
fun distance[i1,i2: Intersection]: Int {
    abs[i1.X.sub[i2.X]].add[abs[i1.Y.sub[i2.Y]]]
}

/***************************************
										Run
***************************************/

run simuler for exactly 1 Drone, exactly 5 Intersection, exactly 2 Receptacle, 3 Commande, 3 EnsembleProduits, 6 int, 5 Chemin


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

