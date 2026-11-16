---
name: llm-council
description: Conseil de 5 conseillers IA pour les décisions importantes. Soumet une question ou un choix à 5 sous-agents aux styles de pensée différents, qui répondent séparément, s'évaluent mutuellement de façon anonyme, puis un président rend un verdict. À utiliser quand l'utilisateur demande « conseil », « council », « demande au conseil », ou veut un avis fiable sur une décision (choix technique, priorité, idée de fonctionnalité, risque).
---

# Conseil LLM (méthode « LLM Council » d'Andrej Karpathy, adaptée à Claude Code)

But : éviter la complaisance d'une première réponse unique. Une décision passe par
5 avis indépendants, une évaluation croisée anonyme, puis une synthèse.

## Étape 1 — Cadrer la question
Reformule la décision en une question claire, avec le contexte utile (code, contraintes,
objectifs de l'utilisateur). Si la question est vague, pose UNE question de précision.

## Étape 2 — 5 conseillers en parallèle
Lance 5 sous-agents (outil Agent, `subagent_type: "general-purpose"`, en parallèle dans
un seul message). Chacun reçoit la même question + le contexte, et un style imposé :

1. **Le Sceptique** — cherche ce qui peut mal tourner, les risques, les coûts cachés.
2. **Le Pragmatique** — la solution la plus simple qui marche maintenant, effort/valeur.
3. **Le Visionnaire** — le long terme, ce que ça ouvre ou ferme pour la suite.
4. **L'Utilisateur** — se met à la place de l'utilisateur final : clarté, plaisir, friction.
5. **L'Expert technique** — faisabilité, qualité, performance, maintenance.

Consigne à chacun : réponse en 150 mots max, une recommandation nette
(OUI / NON / ALTERNATIVE) + 3 arguments + 1 risque. Ne pas chercher à plaire.

## Étape 3 — Évaluation croisée anonyme
Mélange les 5 réponses et étiquette-les A à E (sans le style ni le nom).
Lance 5 nouveaux sous-agents en parallèle : chacun lit les 5 réponses anonymes, les classe
de la plus solide à la plus faible, et signale les erreurs de raisonnement.
Ils ne savent pas quelle réponse vient de quel style.

## Étape 4 — Verdict du président
Toi (Claude) agis comme président :
- additionne les classements (1er = 5 points … 5e = 1 point) ;
- présente à l'utilisateur, dans sa langue et brièvement :
  - **Verdict** : la décision recommandée en une phrase ;
  - **Pourquoi** : les 3 arguments les plus solides du conseil ;
  - **Désaccords** : les points où le conseil était divisé ;
  - **Risque principal** et comment le réduire ;
  - **Score** : le classement final (style révélé à ce moment-là).

Ne tranche pas à la place de l'utilisateur si le conseil est partagé : dis-le clairement.
