// Set this flag on true for debug printing.
SetVerbose("User1", false);

function PolyMor(pol, phi1, phi2)	// Given a "morphism" A -> B and a "morphism" Z[x1, .., xn] -> B construct the associated "morphism" A[x1, .., xn] -> B. 
	if (Type(pol) eq SeqEnum) then
		return [PolyMor(p, phi1, phi2) : p in pol];
	end if;	
	ret := 0;
	mon := Monomials(pol);
	coeff := Coefficients(pol);
	assert(#mon eq #coeff);
	for i in [1..#mon] do
		ret +:= phi1(coeff[i])*phi2(mon[i]);
	end for;
	return ret;
end function;

function RealGCD(a, b)	// Also used for regulator
	vprint User1: "RealGCD(", a, ",", b, ")";
	if (b le 1E-10) then
		return a;
	end if;
	if (a/b le 1E-3) then
		return b;	
	end if;
	k := Floor(b/a);
	return RealGCD(b - k*a, a);
end function;

function Bool2Int(b)
	// Convert a boolean into an integer.
	if b then
		return 1;
	end if;
	return 0;
end function;

function InverseArray(Hp, patchRZ, p)
	// Create an array with for each component of the special an element to invert in the patch to localise away the other components.
	InvArr := [];
	vprint User1: "InverseArray start";
	for i in [1..#Hp`abstract_fibres] do
		vprint User1: "i =", i;
		fibre := Hp`abstract_fibres[i];
		idealFp := fibre`explicit[fibre`patch1]`ideal;
		patch := Hp`patches[fibre`patch1];
		if (Rank(patchRZ[fibre`patch1]) eq 3) then
			RZ<ix,iy,iz> := patchRZ[fibre`patch1];
		else
			RZ<ix,iy,iz,iw> := patchRZ[fibre`patch1];
		end if;
		phi := hom< Parent(Generators(idealFp)[1])->RZ | [ix,iy,iz] >;
		hidegree := false;		
		if (Degree(BaseRing(Parent(Generators(idealFp)[1]))) ne 1) then
			hidegree := true;
			phi2 := hom< BaseRing(Parent(Generators(idealFp)[1])) -> RZ | iw >;
			phi9 := hom< Parent(DefiningPolynomial(BaseRing(Parent(Generators(idealFp)[1])))) -> RZ | iw >;
			defpol := phi9(DefiningPolynomial(BaseRing(Parent(Generators(idealFp)[1]))));
			vprint User1: "defpol before phi2:", DefiningPolynomial(BaseRing(Parent(Generators(idealFp)[1])));
			vprint User1: "defpol =", defpol;
		end if;
		I := patch`ideal_k;
		ideal_id := -1;
		decomp := RadicalDecomposition(I);
		otherideals := ideal<RZ | 1>;
		for j in [1..#decomp] do			
			if (decomp[j] eq idealFp) then
				ideal_id := j;
				if (hidegree) then
					idealZ := ideal< RZ | [PolyMor(a, phi2, phi) : a in Generators(decomp[j])] > + ideal< RZ | p, defpol>;
				else
					idealZ := ideal< RZ | [phi(a) : a in Generators(decomp[j])] > + ideal< RZ | p >;
				end if;
			else
				if (hidegree) then
					tempidealZ := ideal< RZ | [PolyMor(a, phi2, phi) : a in Generators(decomp[j])] > + ideal< RZ | p, defpol>;
				else
					tempidealZ := ideal< RZ | [phi(a) : a in Generators(decomp[j])] > + ideal< RZ | p >;
				end if;				
				otherideals *:= tempidealZ;
			end if;
		end for;
		assert(ideal_id ne -1);
		vprint User1: "otherideals =", otherideals;
		vprint User1: "idealZ =", idealZ;
		
		for a in Generators(otherideals) do
			if not(a in idealZ) then
				InvArr[i] := a;
			end if;
		end for;
		assert(InvArr[i] ne 0);
	end for;
	vprint User1: "InverseArray stop";
	return InvArr;
end function;

function PatchFunctionFieldArray(Hp)
	// Create arrays with function fields and polynomial rings over Q and Z for later reuse (in order to avoid unnecessary reconstruction)
	patchK := AssociativeArray();
	patchR := AssociativeArray();
	patchRZ := AssociativeArray();
	S := Sort(SetToSequence(Keys(Hp`patches)));
	for i in S do
		RZ<ix,iy,iz> := Parent(Hp`patches[i]`eqns[1]);
		OL := BaseRing(RZ);
		if (Degree(OL) eq 1) then
			patchRZ[i] := RZ;
			R<tx,ty,tz> := ChangeRing(RZ, Rationals());
			patchR[i] := R;
			I := ideal < R | Hp`patches[i]`eqns>;
			A3 := AffineSpace(R);
			C := Curve(Scheme(A3, I));
			patchK[i] := FunctionField(C);
		else
			assert (OL eq EquationOrder(OL));
			OL := EquationOrder(OL);
			eqn := DefiningPolynomial(OL);
			RZ2<ix2,iy2,iz2,iw2> := PolynomialRing(Integers(),4);
			phi0 := hom < Parent(eqn) -> RZ2 | iw2 >;
			eqn := phi0(eqn);
			phi1 := hom < OL -> RZ2 | iw2 >;			
			phi2 := hom < RZ -> RZ2 | ix2, iy2, iz2 >;
			patchRZ[i] := RZ2;
			R<tx,ty,tz,tw> := ChangeRing(RZ2, Rationals());
			patchR[i] := R;
			L := PolyMor(Hp`patches[i]`eqns, phi1, phi2);
			Append(~L, eqn);
			I := ideal < R | L >;
			A4 := AffineSpace(R);
			C := Curve(Scheme(A4, I));
			patchK[i] := FunctionField(C);
		end if;
	end for;
	return patchK, patchR, patchRZ;
end function;

function DifferentialArray(Hp, f, patchK, patchR, patchRZ)
	vprint User1: "DifferentialArray(Hp,", f, ", patchK, patchR, patchRZ)";	

	// Calculates the differential array of the differential f*dx.
	assert(Type(Hp) eq CrvRegModel);	// Assert Hp is a regular model
	assert(Type(f) eq FldFunFracSchElt);	// Assert f is an element of a function field.	
	KOrig := Parent(f);	

	S := Sort(SetToSequence(Keys(Hp`patches)));
	patchfunc := AssociativeArray();
	diffarray := AssociativeArray();

	for i in S do
		if (Rank(patchRZ[i]) eq 3) then
			RZ<ix,iy,iz> := patchRZ[i];
			R<tx,ty,tz> := patchR[i];
			phi0 := hom<Parent(Hp`patches[i]`eqns[1])->R | tx, ty, tz>;
			phi00 := hom<Integers()->Integers() | >;
			hidegree := false;
		else
			RZ<ix,iy,iz,iw> := patchRZ[i];
			R<tx,ty,tz,tw> := patchR[i];
			phi0 := hom<Parent(Hp`patches[i]`eqns[1])->R | tx, ty, tz>;
			phi00 := hom<EquationOrder(BaseRing(Parent(Hp`patches[i]`eqns[1])))->R | tw>;
			hidegree := true;
		end if;
		K := patchK[i];		
		x := K.1;
		y := K.2;
		z := K.3;
		if (i[1] eq 1) then
			// Determine function using definitions from source regular model
			w := Genus(Hp`C)+1;
			if (i[2] eq 1) then
				// On this patch you need to transform some things.
				phi := hom < KOrig -> K | [1/y, x/y^w] >;
				patchfunc[i] := -phi(f)/y^2*Differential(y);
			elif (i[2] eq 2) then
				// This should not happen when you take hyperelliptic curves in weighted projective space; see also source for RegularModel.
				assert(false);
			elif (i[2] eq 3) then
				// On this patch you take f*dx, no transformation is needed.
				phi := hom < KOrig -> K | [x, y] >;
				patchfunc[i] := phi(f)*Differential(x);
			end if;
		else
			// Use substitution to get function here
			j := Hp`patches[i]`parent;
			Kparent := patchK[j];
			xp := Kparent.1;
			phi1 := hom < Parent(Hp`patches[i]`eqns[1]) -> K | [K.1, K.2, K.3] >;
			if (hidegree) then
				phi := hom < Kparent -> K | PolyMor(Hp`patches[i]`map, phi00, phi0) cat [tw] >;
			else
				phi := hom < Kparent -> K | phi1(Hp`patches[i]`map) >;
			end if;			
			patchfunc[i] := phi(patchfunc[j]/Differential(xp))*Differential(phi(xp));
		end if;
		vprint User1: "patchfunc", i, "=", patchfunc[i];
		// Find the f such that the differential is f*dx and express everything in terms of the generator.
		fdx := patchfunc[i]/Differential(x);
		eq1dy := Derivative(PolyMor(Hp`patches[i]`eqns[1], phi00, phi0),ty); 
		eq2dy := Derivative(PolyMor(Hp`patches[i]`eqns[2], phi00, phi0),ty);
		eq1dz := Derivative(PolyMor(Hp`patches[i]`eqns[1], phi00, phi0),tz); 
		eq2dz := Derivative(PolyMor(Hp`patches[i]`eqns[2], phi00, phi0),tz); 
		fdx := (eq1dy*eq2dz - eq1dz*eq2dy)*fdx;
		diffarray[i] := fdx;
	end for;

	return diffarray;
end function;

function LocalVanishingOrder(R, I, f, p)
	// Calculate minimum i such that f not in I + (p^i).
	if (f in I) then
		return 1000000; // Infinity 
	end if;
	for i in [1..100] do
		if not(f in (I + Ideal(R!p^i))) then
			vprint User1: "LocalVanishingOrder(R, I,", f, ",", p, ") =", i-1;
			return i-1;
		end if;
	end for;
	vprint User1: "Failed LocalVanishingOrder(", R, ",", I, ",", f, ",", p, ")"; 
	assert(false);
end function;

function DifferentialVanishingOrder(diffarray, coeff, Hp, p, InvArr)
	vprint User1: "DifferentialVanishingOrder(diffarray,", coeff, ", Hp,", p, ", patchRZ)";	

	// Calculates the vanishing order of the differential f*dx.

	ret := 1000000;	// This should be considered as being infinity.	

	for k in [1..#Hp`abstract_fibres] do
		vprint User1: "Abstract fibre", k;
		fib := Hp`abstract_fibres[k];
		i := fib`patch1;
		vprint User1: "Patch nr", i;
		// Step 1: retrieve all data from the diffarray and construct the linear combinations
		fdx := Zero(Parent(diffarray[1][i]));
		if (Rank(Parent(Numerator(fdx))) eq 3) then
			RZ<ix,iy,iz,iv> := PolynomialRing(Integers(),4);
			phiL := [ix,iy,iz];
			hidegree := false;
		else
			RZ<ix,iy,iz,iw,iv> := PolynomialRing(Integers(), 5);
			phiL := [ix,iy,iz,iw];			
			hidegree := true;
		end if;

		for j in [1..#coeff] do
			fdx +:= coeff[j]*diffarray[j][i];
		end for;

		num := Numerator(fdx);
		den := Denominator(fdx);
		factor := LCM([Denominator(t) : t in Coefficients(num) cat Coefficients(den)]);
		factor /:= GCD([Numerator(t) : t in Coefficients(num) cat Coefficients(den)]);
		num *:= factor;
		den *:= factor;
		// Step 2: map everything to a polynomial ring over Z
		phi := hom<Parent(num)->RZ | phiL>;
		num := phi(num);
		den := phi(den);
		vprint User1: "fdx = ", num, "/", den;
		// Step 3: do the Groebner calculations
		gens := Generators(fib`explicit[i]`ideal);
		phi := hom< Parent(gens[1])->RZ | [ix, iy, iz] >;
		phi2 := hom< Parent(InvArr[k])->RZ | phiL >;
		if (hidegree) then
			phi3 := hom< BaseRing(Parent(gens[1]))->RZ | iw >;
			eqn := DefiningPolynomial(BaseRing(Parent(gens[1])));
			phi4 := hom< Parent(eqn)->RZ | iw >;
			eqn := phi4(eqn);
		else
			phi3 := hom< BaseRing(Parent(gens[1]))->RZ | >;
			eqn := RZ!0;
		end if;
		vprint User1: "InvArr[k] =", InvArr[k];
		I := Ideal([PolyMor(a, phi3, phi) : a in gens] cat [eqn, iv*phi2(InvArr[k])-1]);	// TODO: is this really the right ideal?
		ret := Min(ret, LocalVanishingOrder(RZ, I, num, p) - LocalVanishingOrder(RZ, I, den, p));
	end for;
	
//	print "DifferentialVanishingOrder(", coeff, ") =", ret;
	return ret;
end function;


function CompensationFactor(H, p)

	assert(Type(H) eq CrvHyp);	// Assert H is an hyperelliptic curve over the rationals.
	assert(Type(BaseField(H)) eq FldRat);
	assert(IsSimplifiedModel(H));
	assert(Type(p) eq RngIntElt);	// Assert p is a rational prime.
	assert(IsPrime(p));

	ret := 1;

	try
		Hp := RegularModel(H, p);
	catch e
		print "Regular model could not be constructed at p =", p, "for", H;
		print "Compensation factor (and hence the real period) could be off by a power of", p;
		return ret;
	end try; 

	K<x,y> := FunctionField(H);
	patchK, patchR, patchRZ := PatchFunctionFieldArray(Hp);
	InvArr := InverseArray(Hp, patchRZ, p);
	basis := [x^i / y : i in [0..Genus(H)-1]];	// Standard basis for holomorphic differentials: x^i / y * dx
	arewedone := false;
	diffarray := AssociativeArray();

	while (arewedone eq false) do
		arewedone := true;

		// Check that basis elements are well-defined.
		for i in [1..#basis] do
			diffarray[i] := DifferentialArray(Hp, basis[i], patchK, patchR, patchRZ);
		end for;

		for i in [1..#basis] do
			ord := DifferentialVanishingOrder(diffarray, [Bool2Int(i eq j) : j in [1..#basis]], Hp, p, InvArr);
			if (ord le -1) then
				basis[i] := basis[i] * p^(-ord);
				ret *:= p^(-ord);
				diffarray[i] := DifferentialArray(Hp, basis[i], patchK, patchR, patchRZ);
			end if;
		end for;

		// Check that there is nothing vanishing everywhere.
		for i in CartesianPower(Set([0..(p-1)]), #basis) do
			f := &+[K!i[j]*basis[j] : j in [1..#basis]];
			if (f eq 0) then
				continue;
			end if;
			ord := DifferentialVanishingOrder(diffarray, i, Hp, p, InvArr);
			if (ord ge 1) then
				for j in [1..#basis] do
					if (i[j] ne 0) then		
						basis[j] := f/p^ord;
						ret /:= p^ord;
						arewedone := false;
						break;
					end if;
				end for;
				assert(arewedone eq false);
				break;
			end if;
		end for;	

	end while;

	vprint User3: "at p = ", p;
	vprint User3: "basis = ", basis;

	return ret;
end function;

function RealLatticeArea(M)
	// Given a (2g) x g matrix with entries over M, calculate the area of the lattice spanned by its columns.
	g := NumberOfColumns(M);
	assert(NumberOfRows(M) eq 2*g);

	// Calulcate the determinants of all g x g minors.
	dets := [];
	for S in Subsets(Set([1..2*g]), g) do
		N := Matrix([M[s] : s in S]);
		Append(~dets, Abs(Determinant(N)));
	end for;
	Sort(~dets);
	
	// Find the smallest determinant that is not approximately 0.
	ret := -1;
	for d in dets do
		assert( (d le 1E-20) or (d ge 1E-10) );	// Assume all determinants are either almost zero, or distinctively non-zero.
		if (d ge 1E-10) then
			if (ret eq -1) then
				ret := d;
			else	// Check that other determinants are integral multiples.
				ret := RealGCD(d, ret);
				assert(ret ge 1E-10);
				assert(Round(d/ret) - d/ret le 1E-10);
			end if;
		end if;
	end for;
	assert(ret ge 0);

	return ret;
end function;

function ReelePeriode(H)
	// Calculates the real period

	assert(Type(H) eq CrvHyp);	// Assert H is an hyperelliptic curve over the rationals.
	assert(Type(BaseField(H)) eq FldRat);

	Hw := MinimalWeierstrassModel(H);
	Hs := SimplifiedModel(Hw);	// Take simplified models
	g := Genus(H);
	c := 1;	

	for p in BadPrimes(Hs) do
		vprint User1: "Calculating compensation factor for p =", p;
		cf := 1;		
		cf := CompensationFactor(Hs, p);
		c *:= cf;		// Calculate all compensation factors
		vprint User1: "Compensation factor for p =", p, "is", cf;
	end for;

	// Some calculations with big period matrix
	M := BigPeriodMatrix(AnalyticJacobian(Hs));
	MR := [[ 2*Real(M[i][j]) : i in [1..g]] : j in [1..2*g]]; 
	rp := RealLatticeArea(Matrix(MR));

	return rp*c;

end function;

