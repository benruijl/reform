expr F = f(1,2);

attrib f = Symmetric;

apply {
    id all f(x?,y?) = g(x?,y?);
}

attrib g = Symmetric;

apply {

}