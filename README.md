# Show that SL(2,R) is a smooth manifold by explicitly giving an atlas

Replace `Title` with the title of your project, and *rewrite* this markdown file to describe the following:

1. The topic of your project. State the relevant background, definitions, and theorems, using natural language. Add any necessary references.
2. The structure of the lean project itself. How is your code organized?
3. The main definitions you constructed and/or theorems you formalized, and where they can be found in your code.
4. Any other relevant information.

# 1. THE TOPIC OF THE PROJECT
In this project, I will attempt to show that SL(2,R) is a smooth manifold, by giving an atlas on it.

Below is some necessary definitions:
*Definition 1:* A topological space M is locally Euclidean of dimension n if for every point p of M, there is an open neighbourhood U of p such that U is homeomorphic to an open subset of ℝⁿ.

`Notation:` From definition 1, the pair (U, φ: U → ℝⁿ ) is called a chart, where φ: U → ℝⁿ is a homeomophic when restric the range to the open subset φ(U).

*Definition 2:*  A topological manifold is Haursdorff, second countable and locally Euclidean space. If the space is locally Euclidean of dimension n, the we say the manifold of dimension n.

*Definition 3: (Compatible charts)* : Given two charts (U, φ: U → ℝⁿ ) and (V,  φ': V → ℝⁿ ) on a topological manifold. Then they are called C∞ compatible, or just compatible,  if the two maps
φ ∘ (φ')⁻¹:φ'(U ∩ V ) → φ(U ∩ V )              and      φ'  ∘ (φ)⁻¹  : φ(U ∩ V ) → :φ'(U ∩ V )  
are smooth maps

*Definition 4: (atlas)* : A C∞ atlas or simply an atlas on topological space M is a family of charts {(Uᵢ, φᵢ )}, where any pairs of chart is a compatible and M = ∪ Uᵢ (M is covered by the open family Uᵢ).

From this definition, we call an atlas 𝓤 maximal  if we can not find another atlas that contains 𝓤. Then we can define the smooth manifold:

*Definition 5: (smooth manifold)* A smooth manifold is a topological space M equipped with a maximal atlas. 

Theoretically, in order to prove that a topological manifold M is smooth, we have to find a maximal atlas. However, the following property tells us a simpler way to do that:

`Proposition: `Any atlas 𝓤 = {(Uᵢ, φᵢ )} on a locally Euclidean space is contained in a unique maximal atlas.

With this proposition, we only need to construct a C∞ atlas then M is automatically smooth. 

Now we focus on SL(2,R). First we can identiy the matrix group SL(2,R) with a subset of ℝ⁴ as follows: 
*Definition 6:* SL(2,R) = {(x,y,z,t) ∈ ℝ⁴| xy -zt =1}

Since ℝ⁴ is second countable and Haursdorff, SL(2,R) is also second countable and Haursdorff, so we only need to construct a C∞ atlas as noted above. Note that SL(2,R) is covered by 

U₁ = {(x,y,z,t) ∈ ℝ⁴| xy -zt =1 and x ≠ 0}       and  U₂ = {(x,y,z,t) ∈ ℝ⁴| xy -zt =1 and z ≠ 0},

So we define two open sets in ℝ³ as follows: 

V₁ = {(x,z,t) ∈ ℝ³|  x ≠ 0}                        and  V₂ = {(x,y,z) ∈ ℝ³| z ≠ 0}

Then the projection map: φ₁(x,y,z,t) = (x,z,t) give a is a map from U₁ to V₁. Similarly, the map 
φ₁(x,y,z,t) = (x,y,z) is from U₂ to V₂. Moreover, these map are invertible, so they are homeomorphic from Uᵢ to Vᵢ. For example, consider U₁ and U₂, we have 

φ₁ ∘ (φ₂)⁻¹(x,y,z) = φ₁(x,y,z, (xy-1)/z)= (x,z,(xy-1)/z)

The component of this map are just rational polynomials, so it is clear that they are smooth on 
φ₂(U₁∩ U₂). We can do similarly for the other pairs, and there are 4 pairs in total. This show that SL(2,R) is a smooth manifold. 

# 2. The Structure of the lean code 

The code is divided in 4 mains part and it is based on the instance of manifold structure of the real field - the file Real.lean.
1. Definition of SL(2,R): In this part I gave the definition for the group SL(2,R) and impose topology structure on it. I also introduce some lemmas/ theorems that I used in the second part of 

2. Construction charts: In this part, I define the Partial homemorphism from SL(2,R) to ℝ × ℝ × ℝ. This includes of defining source set, target set, homeomorphism and its inverse as well as proving the continuity of the related maps. 

3. Construction of Charted space.

4. Give instance of smooth manifold structure of SL(2,R). 

# 3. The Structure of the lean code 

The theorems/ definitions I constructed were: 
1. line 25: The definition of the set SL(2,R).

2. line 90,138: constructed of the two charts. I could fill in almost all of them except for the last one, since I don't know how to deal with the Goal ContinuouswithinAt, so I left it with a sorry.

3. line 183: Construct a charted space.

4. line 200: Set up manifold structure. At first I think it would be similar to the real line instance. Turn out it is not, or at least I don't know how to unfold the goal. 


# 4. Reference: 

The main reference I used for this project are: 

1. Tu LW. Manifolds. InAn Introduction to Manifolds 2011 May 5 (pp. 47-83). New York, NY: Springer New York.

2. Thread Explicitly giving an atlas to make SL(2,R) a smooth manifold: https://math.stackexchange.com/questions/3539708/explicitly-giving-an-atlas-to-make-sl2-mathbbr-a-smooth-manifold

3. The Real.lean and Sphere.lean for reference on how to give the lean code.


