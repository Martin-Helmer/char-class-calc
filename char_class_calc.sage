r"""
Package to compute Segre classes, Chern-Schwartz-MacPherson classes and the Euler characteristic of projective varieties.

AUTHOR:
   -- Martin Helmer
"""

########################################################################
#  Author: Martin Helmer 
#  Email: <mhelmer2@uwo.ca> or <martin.helmer2@gmail.com>       
#
#
########################################################################


from sage.interfaces.phc import phc
class characteristic_class_object:
    """
    A container for the results of characteristic class computation, allowing the storage of steps 
    of the computation, allowing potential access and viewing at a later time without recomputing. 
    """
    def __init__(self, K):
        '''
        INPUT:
            K: A homogeneous ideal K in the polynomial ring k[x0,...,xn], where k is some field, 
            either QQ (the rationals) or some finite field in prime characteristic, i.e. GF(32749). 
        '''
        if (K.is_homogeneous())!=True:
            K=K.homogenize();
            print "Input ideal was not homogeneous, proceeding using homogenized ideal = ", K
        self.R1=K.ring()
        self.K=K;
        self.kk=K.base_ring()
        self.x=self.R1.gens()
        self.Kl=self.K.gens()
        self.n=len(self.x)
        self.R=PolynomialRing(self.kk,[c for c in self.x]+['T'])
        self.T=self.R.gens()[self.n]
        self.polar_dict={}
        self.csm_hypersurface_dict={}
        self.segre_proj_deg=[];
        self.B= PolynomialRing(ZZ,'H');
        self.H = self.B.gen();
        self.A = self.B.quotient((self.H)^(self.n), 'h');
        self.h = self.A.gen();
        self.csm=0*self.h;
        self.segre=0*self.h;
        self.S=Subsets(range(0,len(self.Kl)),submultiset=True).list()
        del self.S[0]
        self.euler=0*self.h;
    
    def get_csm(self):
        if self.csm==0:
            char_class.csm(self.K,self)
        else:
            print "csm class: ",self.csm
        return self.csm;    
    def get_segre(self):
        if self.segre==0:
            char_class.segre(self.K,self)
        else:
            print "segre class: ",self.segre
        return self.segre;    
    def get_euler(self):
        if self.euler==0:
            char_class.csm(self.K,self)
        else:
            print "Euler characteristic: ",self.euler.list()[self.n-1]
        return self.euler;    
    
    def get_chow_ring(self):
        return self.A;
    
    def get_csm_hyper_dict(self):
        if self.csm==0:
            char_class.csm(self.K,self)
        return self.csm_hypersurface_dict;
    
    def get_polar_dict(self):
        if self.csm==0:
            csm(self.K,self)
        return self.polar_dict;
        
class characteristic_class:
    """
    A class to compute characteristic classes, has methods to compute the Segre class, Chern-Schwartz-MacPherson
    class and the Euler characteristic.
    EXAMPLES: # work in P^3, do the ideal of the twisted cubic
        sage: r=3
        sage: R=PolynomialRing(GF(32749),  ['x%s'%c for c in range(0,r+1)])
	sage: x=R.gens()
        sage: I=R.ideal(x[1]*x[3]-x[2]^2, x[2]*x[0]-x[3]^2,x[1]*x[0]-x[2]*x[3])
        sage: csm_class_I=char_class.csm(I)
        csm class of input ideal:  2*h^3 + 3*h^2
        sage: csm_class_I.csm
        2*h^3 + 3*h^2
        sage: csm_class_I.polar_dict
        {'[1, 2]': [1, 3, 5, 3], '[0, 2]': [1, 3, 5, 3], '[0, 1, 2]': [1, 5, 10,
        6], '[2]': [1, 1, 1, 1], '[0, 1]': [1, 3, 5, 3], '[0]': [1, 1, 1, 0],
        '[1]': [1, 1, 1, 0]}
        sage: csm_class_I.csm_hypersurface_dict
        {'[1, 2]': 4*h^3 + 4*h^2 + 4*h, '[0, 2]': 4*h^3 + 4*h^2 + 4*h, '[0, 1,
        2]': 4*h^3 + 3*h^2 + 6*h, '[2]': 4*h^3 + 4*h^2 + 2*h, '[0, 1]': 4*h^3 +
        4*h^2 + 4*h, '[0]': 3*h^3 + 4*h^2 + 2*h, '[1]': 3*h^3 + 4*h^2 + 2*h}
        sage: csm_class_I.euler
        2*h^3
        sage: csm_class_I.get_euler()
        Euler characteristic:  2
        2*h^3
        sage: csm_class_I.get_segre() 
        The Segre class is:  -10*h^3 + 3*h^2
        -10*h^3 + 3*h^2
        sage: # to compute just the segre class
        sage: segre_class_I=char_class.segre(I)
        sage: The Segre class is:  -10*h^3 + 3*h^2
        sage: segre_class_I.segre
        -10*h^3 + 3*h^2
        sage: euler_class_I=char_class.euler(I)
        sage: euler_class_I.euler
        2*h^3
        sage: euler_class_I.csm
        2*h^3 + 3*h^2
        
          
    """
    def degree_check(self,I):
        """
        Input:
            I -- a polynomial ideal
        Output:
            checkv -- a boolean, true if all generators of I have the same degree, false if they have different degrees    
        """
        checkv=True;
        d=I.gens()[0].degree();
        for f in I.gens():
            if f.degree()!=d:
                checkv=False;
                break;
        return checkv;
        
    def projective_degree(self, char_class_obj,J,print_level='quiet',sym_or_num='sym'):
        """
        Input:
            char_class_obj -- An object of the class characteristic_class_object, which is a container for 
                              characteristic class calculation info
            J -- A list of polynomials generating a polynomial ideal, 
                 all generators must have the same degree (or be 0)
            sym_or_num -- Determines if the calculations are done symbolically using the vector_space_dimension() 
                          command, which uses Groebner basis, or numerically using PHCPack. Set to 'sym' for symbolic
                          computations by default, to use phc we do sym_or_num='phc'
        Output:
            polarList -- a list of the projective degrees, (g0,...,gn), of the rational map specified by the ideal J                                       
        """
        
                    
        R=char_class_obj.R
        R1=char_class_obj.R1
        x=char_class_obj.x
        kk=char_class_obj.kk
        T=char_class_obj.T
        n=char_class_obj.n
        
        Jg=list()
        val=0;
        for w in J:
            if w!=0:
                Jg.append(w)
        Js=char_class_obj.R1.ideal(Jg);
        if self.degree_check(Js):
            val=(n-1)-Js.dimension();
            d=Js.gens()[0].degree()
        polarList=[1]
        for k in range(1,n):
            # if the coefficient field is the rationals the default random element call 
            #doesn't do a very good job of creating random rational numbers so we change it
            if val>k:
                polarList.append(d^k);
            else:
                if kk==QQ:
                    W=sum([R.ideal([sum([kk.random_element(700,100,distribution='uniform')*c for c in J])]) for i in range(0,k)])
                    Xs=sum([R.ideal([sum([kk.random_element(700,100,distribution='uniform')*c for c in x])]) for i in range(0,n-k-1)])+R.ideal([sum([kk.random_element()*c for c in x])-1])
                    EqT=R.ideal([sum([1-T*kk.random_element(700,100,distribution='uniform')*c for c in J])])
                else:
                    W=sum([R.ideal([sum([kk.random_element(700,100,distribution='uniform')*c for c in J])]) for i in range(0,k)])
                    Xs=sum([R.ideal([sum([kk.random_element(700,100,distribution='uniform')*c for c in x])]) for i in range(0,n-k-1)])+R.ideal([sum([kk.random_element()*c for c in x])-1])
                    EqT=R.ideal([sum([kk.random_element()-T*kk.random_element(700,100,distribution='uniform')*c for c in J])])
                Wt=W+Xs+EqT
                if sym_or_num=='phc':
                    Wg=list()
                    for w in Wt.gens():
                        if w!=0:
                            Wg.append(w)
                    v13=phc.blackbox(Wg,R);
                    polarList.append(len(v13.solutions()));
                else:
                    
                    if print_level=='loud':
                        print "Wt length= ", len(Wt.gens())
                        print "Wt= ", Wt.gens()
                    polarList.append(Wt.vector_space_dimension());     
                
        
        if print_level=='loud':
            print "The projective degree is: ", polarList
           
        return polarList;
        
    def segre(self, K,segre_obj=None,print_level='quiet',sym_or_num='sym',print_type='plain'):
        """
        Input:
            K -- a homogeneous ideal in a polynomial ring over a finite field of large prime characteristic 
                 or over the rationals, if all generators are not of the same degree an error message is displayed
            segre_obj -- optional, object of class characteristic_class_object, if specifed the information in 
                         the object is used for calculations
            print_level -- optional, default value is 'quiet', so only the final value is outputed, if set to 'loud'
                           some extra info is printed
            sym_or_num -- Determines if the calculations are done symbolically using the vector_space_dimension() 
                          command, which uses Groebner basis, or numerically using PHCPack. Set to 'sym' for symbolic
                          computations by default, to use phc we do sym_or_num='phc' 
            print_type -- optional, 'plain' is default and prints outputs in plain text. 'latex' prints nice
                          latexed output. 
        Output:
            segre_obj -- An object of class characteristic_class_object. Holds the information 
                         computed by the method segre, segre_obj.segre holds the segre class, 
                         segre_obj.A holds the chow ring that the segre class is in, segre_obj.h is the generator
                         of the chow ring.                                
         EXAMPLES: #segre embedding of P^1xP^2  in P^5 defined by minors
            sage: r=5
            sage: R=PolynomialRing(GF(32749),  ['x%s'%c for c in range(0,r+1)])
	    sage: y=R.gens()
            sage: K=R.ideal(y[0]*y[4]-y[1]*y[3],y[0]*y[5]-y[2]*y[3],y[1]*y[5]-y[4]*y[2])
            sage: csm_class_K=char_class.segre(K)
            The Segre class is:  -48*h^5 + 24*h^4 - 10*h^3 + 3*h^2
            sage: csm_class_I.segre
            -48*h^5 + 24*h^4 - 10*h^3 + 3*h^2
            sage: csm_class_I.get_csm()
            csm class of input ideal:  6*h^5 + 9*h^4 + 8*h^3 + 3*h^2
            6*h^5 + 9*h^4 + 8*h^3 + 3*h^2
        """
        if self.degree_check(K):
            if segre_obj is None:
                segre_obj=characteristic_class_object(K)
            if sym_or_num!='sym' and segre_obj.kk!=QQ:
                print "Error: Numeric calculations must be done over Q"
                return
            h=segre_obj.h;
            d=K.gens()[0].degree()
            n=segre_obj.n;
            n1=n-1;
            g=self.projective_degree(segre_obj,K.gens(),print_level,sym_or_num)
            poly=sum([g[i]*h^i*(1+d*h)^(n1-i) for i in range(0,n)])
            segre_obj.segre=1-poly*sum([binomial(n1+i,i)*(-d*h)^i for i in range(0,n)])
            if print_type=='none':
                print("")
            elif print_type=='latex':
                html('')
                html('The Segre class is $s(V,\mathbb{P}^%s)\;=\;%s$ in $\mathbb{Z}[h]/h^%s$'%(latex(segre_obj.n),latex(segre_obj.segre),latex(segre_obj.n)))
            else:
                print "The Segre class is: ",segre_obj.segre;
            return segre_obj; 
        else:
            print "To calculate the segre class all generators of the input ideal must have the same degree, please enter generators of the same degree"   
            return;  
        
        
        
    def euler(self, K,csm_obj=None,print_level='quiet',print_type='plain'):
        """
        Input:
            K -- a homogeneous ideal in a polynomial ring over a finite field of large prime characteristic 
                 or over the rationals, if all generators are not of the same degree an error message is displayed
            csm_obj -- optional, object of class characteristic_class_object, if specifed the information in 
                         the object is used for calculations
            print_level -- optional, default value is 'quiet', so only the final value is outputed, if set to 'loud'
                           some extra info is printed
            print_type -- optional, 'plain' is default and prints outputs in plain text. 'latex' prints nice
                          latexed output. 
        Output:
            csm_obj -- An object of class characteristic_class_object. Holds the information 
                         computed by the method csm, which is called by euler, 
                         csm_obj.euler holds the euler class, csm_obj.csm holds the csm class,
                         csm_obj.A holds the chow ring that the csm class is in, csm_obj.h is the generator
                         of the chow ring.                                
        """
        if csm_obj is None:
            csm_obj=characteristic_class_object(K)
        csm_obj=self.csm(K,csm_obj,print_level=print_level,print_type=print_type)
        if print_type=='none':
            print("")
        elif print_type=='latex':
            html('')
            html('The Euler class is $\chi\;=\;%s$ in $\mathbb{Z}[h]/h^%s$'%(latex(csm_obj.euler),latex(csm_obj.n)))
        else:
            print "Euler class is ",csm_obj.euler
        return csm_obj;    
    
    def csm(self,K,csm_obj=None,print_level='quiet',sym_or_num='sym',print_type='plain'):
        """
        Input:
            K -- a homogeneous ideal in a polynomial ring over a finite field of large prime characteristic 
                 or over the rationals, if all generators are not of the same degree an error message is displayed
            csm_obj -- optional, object of class characteristic_class_object, if specifed the information in 
                         the object is used for calculations             
            print_level -- optional, default value is 'quiet', so only the final value is outputed, if set to 'loud'
                           some extra info is printed
            sym_or_num -- Determines if the calculations are done symbolically using the vector_space_dimension() 
                          command, which uses Groebner basis, or numerically using PHCPack. Set to 'sym' for symbolic
                          computations by default, to use phc we do sym_or_num='phc                
            print_type -- optional, 'plain' is default and prints outputs in plain text. 'latex' prints nice
                          latexed output. 
        Output:
            csm_obj -- An object of class characteristic_class_object. Holds the information 
                         computed by the method csm, 
                         csm_obj.euler holds the euler class, csm_obj.csm holds the csm class,
                         csm_obj.A holds the chow ring that the csm class is in, csm_obj.h is the generator
                         of the chow ring.
                         

        EXAMPLES: #segre embedding of P^1xP^2  in P^5 defined by minors
            sage: r=5
            sage: R=PolynomialRing(GF(32749),  ['x%s'%c for c in range(0,r+1)])
	    sage: y=R.gens()
            sage: K=R.ideal(y[0]*y[4]-y[1]*y[3],y[0]*y[5]-y[2]*y[3],y[1]*y[5]-y[4]*y[2])
            sage: csm_class_K=char_class.csm(K)
            csm class of input ideal:  6*h^5 + 9*h^4 + 8*h^3 + 3*h^2
            sage: csm_class_I.csm
            6*h^5 + 9*h^4 + 8*h^3 + 3*h^2
            sage: csm_class_I.euler
            6*h^5
                                                           
        """
        if csm_obj is None:
            csm_obj=characteristic_class_object(K)
        if sym_or_num!='sym' and csm_obj.kk!=QQ:
            print "Error: Numeric calculations must be done over Q"
            return
        csm_hyp=0
        n=csm_obj.n
        polarHere=[1]+[0]*(n-1)
        count=0
        csm_total=0
        n1=n-1
        h=csm_obj.h
        for s in csm_obj.S:
            hyper=prod([csm_obj.Kl[c] for c in s])
            #print hyper.degree()
            J=hyper.gradient();
            polar_list=self.projective_degree(csm_obj,J,print_level,sym_or_num);
            csm_obj.polar_dict[str(s)]=polar_list
            csm_hyp=(1+h)^(n)-sum([ polar_list[i]*(-h)^i*(1+h)^(n1-i) for i in range(0,n)])
            csm_obj.csm_hypersurface_dict[str(s)]=csm_hyp;
            csm_total=csm_total+(-1)^(len(s)+1)*csm_hyp
            if print_level !='quiet':
                print "The polar degrees for the hypersurface product of ",s," is ", polar_list
                print "csm class of ",hyper," = ",csm_hyp;
        csm_obj.csm=csm_total;
        csm_obj.euler=csm_total.list()[n1]*h^n1;
        if print_type=='none':
            print("")
        elif print_type=='latex':
            html('')
            html('$c_{SM}\;=\;%s$ in $\mathbb{Z}[h]/h^{%s}$'%(latex(csm_total),latex(csm_obj.n)))
        else:
            print "csm class: ", csm_total        
        return csm_obj; 
        
################################

# The unique instance of the characteristic_class class to be used for computing all things computed by the class
char_class=characteristic_class()
