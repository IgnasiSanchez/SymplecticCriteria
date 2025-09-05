function EllipticCurveRedMod5(T)
    return MinimalModel(EllipticCurve([1-T,-T,-T,-5*(T^3+2*T^2-T),-T*(T^4+10*T^3-5*T^2+15*T-1)]));
end function;

