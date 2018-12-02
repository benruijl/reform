#![feature(test)]
extern crate test;

extern crate ndarray;

extern crate reform;

use test::Bencher;

use ndarray::{ArrayView, ArrayView1, ArrayView2};

use reform::poly::raw::zp;
use reform::poly::raw::zp::{ufield, FastModulus};

/*
n = 8;
p = NextPrime[2^30, -1];
a = Table[RandomInteger[{0, p - 1}], {n}, {n}];
b = Table[RandomInteger[{0, p - 1}], {n}];
x = LinearSolve[a, b, Modulus -> p];
*/

#[bench]
fn zp_solve8x8(b: &mut Bencher) {
    let a: ArrayView2<ufield> = ArrayView::from_shape(
        (8, 8),
        &[
            581962757, 982179354, 897967976, 357232738, 498748862, 908237485, 392276714, 567274827,
            800307988, 731183116, 527618090, 758539184, 935012179, 980221544, 67282650, 714495896,
            594065329, 1006350964, 34662131, 407424025, 720725329, 999245740, 972565402, 264934098,
            387399233, 932290789, 881658979, 1007562945, 747007532, 864164245, 872577773,
            173273274, 46112073, 570804678, 660103286, 581868710, 495985726, 384510380, 181913409,
            1319492, 881709382, 719970231, 103435931, 459658048, 556902309, 581721222, 787078486,
            429455907, 729363464, 697159446, 749945145, 513488397, 413384490, 9508676, 155942484,
            41084927, 541953164, 205847091, 879617734, 527327832, 510489751, 229793941, 832570671,
            277986528,
        ],
    )
    .unwrap();
    let bb: ArrayView1<ufield> = ArrayView::from_shape(
        (8,),
        &[
            425624807, 856141991, 404211143, 444057653, 229902237, 386423009, 1000875508,
            1000086555,
        ],
    )
    .unwrap();
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    let x: ArrayView1<ufield> = ArrayView::from_shape(
        (8,),
        &[
            303589260, 265233435, 9242804, 82274293, 524235948, 219089428, 895674455, 107421286,
        ],
    )
    .unwrap();
    b.iter(|| {
        let r = zp::solve(&a, &bb, p).unwrap();
        assert_eq!(r, x);
        r
    });
}

#[bench]
fn zp_solve16x16(b: &mut Bencher) {
    let a: ArrayView2<ufield> = ArrayView::from_shape(
        (16, 16),
        &[
            541789347, 952407337, 598950773, 833151099, 905342757, 540664739, 468574564, 616269547,
            274837570, 826096610, 59889728, 687346910, 85817616, 576605199, 286021570, 41076034,
            560587833, 243809187, 747887801, 1044063775, 1043228509, 67644421, 1007154703,
            507313682, 963723232, 398865936, 740630865, 2717104, 952505861, 1022442471, 189722701,
            327032246, 396357759, 550300850, 496757321, 432172994, 170868086, 217179874, 359490917,
            367735827, 617740561, 499252481, 994754632, 680175291, 541737012, 195420602, 395047854,
            11359323, 146582048, 922079679, 241259278, 944975292, 333956066, 1007883051, 344631626,
            1013725936, 854641000, 947533833, 616603580, 48612541, 412652840, 440127063, 224493734,
            431616788, 1054301269, 950812720, 1018369627, 742156908, 711445515, 941480410,
            870494277, 43347289, 594227017, 722861628, 426578231, 90415810, 449832789, 949691979,
            380242593, 498871359, 30037647, 460909113, 975445293, 405722204, 854026168, 8886438,
            145547776, 526842112, 553317892, 14225450, 264028230, 26201045, 74582031, 10005951,
            420290997, 1059870202, 382445788, 469498755, 918946020, 812398545, 377456248, 70721605,
            864432506, 762376405, 94245200, 1028045746, 889991286, 834130262, 469774539, 638462850,
            625593050, 551527953, 559168801, 1031128373, 653392454, 1062115069, 464795569,
            488019270, 31972695, 191308958, 603735248, 731196169, 902881642, 420751256, 627253401,
            1029548919, 1042773329, 621846585, 59184576, 650541013, 313064759, 360087163,
            609163036, 1035148702, 951084804, 882404707, 1013497307, 51095829, 826848205, 72577486,
            389181890, 638204245, 601878075, 837883725, 472791375, 19913027, 109373853, 85468865,
            949253992, 1047163318, 980344793, 731407802, 18856263, 466859367, 289475471, 972595694,
            1057583564, 781543452, 574348269, 964532849, 474555827, 309630410, 191626044,
            613315498, 1011778802, 1072739944, 672720184, 217644314, 501907777, 705000452,
            353104401, 573697213, 451594526, 193775199, 234616853, 139537104, 346916595, 380489875,
            335908982, 845162151, 555037639, 511094171, 343574575, 711595635, 752335996, 52699037,
            390069788, 765877200, 594330783, 583803036, 980521636, 419724206, 977897624, 409731801,
            761531990, 337753788, 555271773, 126567632, 562514525, 941356855, 533049671, 385361239,
            849390052, 65779848, 836196510, 1024587914, 292325939, 33875595, 691041521, 100973186,
            464943768, 920889947, 1041081535, 1064576685, 184018949, 1044754502, 689728332,
            719992166, 1019450628, 128685332, 805767633, 218223408, 640785999, 399232861,
            563837620, 912952199, 475733562, 191236191, 910057978, 472093262, 239302008, 477729110,
            119994649, 931013163, 398277657, 411901799, 110119113, 4783480, 817871159, 423404945,
            1047394154, 67190473, 113573359, 655221054, 132179364, 85318524, 442706414, 441594241,
            51809123, 296388362, 819636270, 650905305, 791616760, 224893440, 329142491, 798151467,
        ],
    )
    .unwrap();
    let bb: ArrayView1<ufield> = ArrayView::from_shape(
        (16,),
        &[
            326511598, 80166637, 415968530, 501614771, 701896421, 748634219, 819355078, 869776946,
            861821996, 455439302, 599620959, 706934539, 277493435, 71408846, 650116041, 126635775,
        ],
    )
    .unwrap();
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    let x: ArrayView1<ufield> = ArrayView::from_shape(
        (16,),
        &[
            274439590, 632793464, 1031201202, 715041664, 753670802, 41995709, 40020270, 794766464,
            59590494, 298950464, 363067051, 398069851, 222787042, 883284060, 299907438, 246318846,
        ],
    )
    .unwrap();
    b.iter(|| {
        let r = zp::solve(&a, &bb, p).unwrap();
        assert_eq!(r, x);
        r
    });
}

#[bench]
fn zp_solve32x32(b: &mut Bencher) {
    let a: ArrayView2<ufield> = ArrayView::from_shape(
        (32, 32),
        &[
            757839730, 804608821, 760341671, 918459263, 166058317, 180492433, 772979413, 397431266,
            583054545, 9313727, 478174217, 52346148, 470757473, 336444777, 609196503, 758008874,
            505331129, 288732563, 390199763, 920209062, 306882870, 859965077, 146529871, 182585075,
            938362118, 1021302367, 804020139, 639089024, 388061311, 437879678, 296741926,
            1038037057, 818553266, 125294452, 1014483479, 604260927, 973714252, 307105253,
            482478015, 955119319, 106356337, 595630284, 661747834, 577332014, 716186954, 200473854,
            432238124, 299399369, 503221981, 994912644, 725340629, 641780005, 672809198, 257166368,
            259667202, 479434024, 716183549, 428390100, 658248829, 524415220, 806480087, 744475862,
            303791977, 856373684, 366402412, 115081506, 168895069, 1058141903, 938267388,
            790950372, 530879992, 338272094, 608048294, 678993181, 703978210, 194876833, 378780638,
            863211523, 529475161, 2579030, 225279862, 944206102, 229844652, 405169251, 197841475,
            686861687, 458971899, 557262186, 633801047, 324257586, 40181251, 1024418057, 645357467,
            872692356, 385087109, 925324408, 439161855, 450972709, 339863957, 390449947, 520973714,
            193188284, 410236332, 111369842, 407286000, 499767992, 209927956, 884141856, 892174042,
            162271653, 478838851, 627385182, 362099210, 347289879, 711448356, 568229985, 352491231,
            749063622, 906257923, 501926736, 70721871, 493358544, 638218440, 176436373, 159197484,
            18675610, 85729960, 577963459, 759843236, 82627979, 753915052, 291503253, 915536244,
            922494821, 954565740, 297276491, 547347209, 1045449032, 290716230, 269990896,
            934324758, 382626263, 206468990, 1061609790, 174777097, 1051889357, 520459594,
            155068429, 72216442, 370397407, 8893634, 847573480, 338457716, 292784428, 518513791,
            749849976, 877274578, 386687132, 528075188, 147092281, 827149343, 726106375, 579849428,
            665351167, 290453848, 561981203, 967594926, 1008584837, 720304856, 973770259,
            893385608, 419959098, 266438053, 296886879, 61064724, 851966376, 642656275, 891141457,
            989243127, 308828227, 728266530, 418753806, 519296856, 801189870, 531481981, 626107950,
            835351863, 947091577, 660143592, 643647718, 309217010, 644202040, 218526137, 810506993,
            773691638, 309321455, 181125302, 961699434, 250843259, 328161870, 315415991, 666360224,
            787408172, 85770639, 1057680942, 439715838, 458638631, 870042135, 987918882, 599846746,
            537709390, 286908279, 685001626, 363248416, 619843297, 379195553, 386355081, 284584732,
            357399492, 234082639, 636291447, 967510402, 248058358, 510891606, 747344745,
            1069759167, 658320065, 824482141, 284163911, 861763415, 216464577, 1069543895,
            267407279, 601962227, 534090649, 886500753, 646132656, 99538437, 302370075, 973970028,
            398928113, 516966727, 864336383, 1011404045, 166828265, 654271072, 804855228,
            730537651, 186713053, 851839027, 255202281, 283508095, 117387189, 855513542, 878564395,
            660339488, 469031814, 338243771, 269917666, 322694682, 871523236, 496897250, 805274379,
            194050448, 594026717, 59866423, 751630957, 1028481034, 228282360, 672772716, 799420990,
            103783445, 71990712, 239231951, 841321675, 265713554, 969986711, 238858124, 1031910963,
            476665160, 810027884, 558654250, 823484303, 1017412655, 108406177, 574100003,
            230994202, 34981507, 1019178334, 435430963, 910027440, 413454311, 905756673, 612031742,
            180486709, 183262405, 909679891, 758335739, 1032329163, 452748064, 321444342,
            1071742407, 104597574, 890707756, 14945865, 888757234, 82375644, 377374642, 619984213,
            431623230, 298494618, 321436350, 232844384, 698383592, 418243697, 708345507, 274032544,
            812941074, 468280759, 266843272, 530517829, 235627886, 656008475, 798138957, 947412552,
            770630828, 419449851, 219722261, 205809749, 16444809, 54071425, 686849072, 1635289,
            679400884, 128500093, 517905857, 352891668, 686272980, 1024380189, 180058737,
            975649894, 455540890, 1066659064, 48882367, 40129353, 77172811, 362005432, 268216613,
            1046740921, 231685351, 51037063, 614664253, 429500116, 991689128, 145357257, 990291783,
            200345275, 307580130, 808366657, 893425780, 122624491, 599384635, 40854135, 700248964,
            853055430, 482664102, 34438922, 100032000, 256063278, 433023508, 274487983, 189625039,
            771850792, 781979293, 862973949, 402597921, 47565365, 855168888, 180497905, 890417726,
            362427546, 1015970480, 582095191, 424464378, 890761589, 1070170011, 359817129,
            558744843, 628067773, 90193717, 950895788, 958213265, 324947359, 576446927, 383998194,
            480848557, 734473431, 963089388, 510726459, 291311065, 575811287, 1020851538,
            442458597, 105706344, 231823, 10284185, 753007484, 575018098, 387651303, 874230983,
            375794196, 906372460, 457759487, 452661382, 63050470, 308878873, 763986661, 979248836,
            703694187, 965504670, 411134591, 684864519, 31026841, 488004232, 1013194048, 264153999,
            38198579, 712571693, 553952620, 433814820, 482964675, 939547779, 606508937, 495321302,
            241240159, 149714098, 1065425151, 74797200, 850679094, 758033744, 518164693, 905121484,
            385586950, 913925007, 550771987, 21630323, 129762775, 316702224, 746015576, 231292377,
            649692196, 1036828783, 784269742, 312138189, 297665646, 973398275, 716440018,
            611602258, 180169409, 859140332, 102081581, 587772407, 226281844, 320178280, 16153165,
            266971018, 894144209, 845027238, 222100485, 195194273, 311399073, 542844582, 191058424,
            244947022, 166658804, 188836203, 306754972, 65934446, 965577171, 580049948, 596603312,
            142044550, 257796391, 274155644, 890848521, 1043910153, 259709821, 178362983,
            766927903, 536025211, 291879726, 493968272, 394381661, 357446241, 688924843, 622918949,
            987908448, 7457741, 845544569, 1008478971, 991108837, 555794364, 214052964, 387175852,
            290749822, 427281536, 167052736, 751092932, 341813505, 535179856, 395077342, 848638896,
            333682953, 264805195, 132844619, 487125723, 891967509, 1026302811, 52233932, 764270533,
            770255621, 59087438, 699591934, 506217331, 1023316814, 1061579417, 681520241,
            856372665, 473616309, 967967017, 1043676642, 990392143, 87037872, 164595373, 184065280,
            41670886, 645616149, 488221288, 48771295, 309599665, 199130393, 1018608705, 440984069,
            702311460, 89065142, 1001082688, 905276400, 512424405, 175860819, 851363577, 734274642,
            40610494, 929995924, 762911693, 1031990513, 839378503, 812426, 52008128, 233850420,
            736364970, 354964279, 559657273, 150710663, 950692835, 1060738432, 115362042,
            742301993, 897831434, 509589778, 863333973, 200738871, 31805248, 593327234, 56330974,
            177502550, 611166154, 454920959, 590659699, 163898919, 325796535, 56694212, 951009533,
            1030920059, 255303565, 1039132264, 1008246032, 793102541, 365800443, 344180438,
            395174483, 605443373, 734419992, 544667172, 305273067, 714770070, 218662142, 731052692,
            972321116, 598989795, 837371742, 616090263, 1008573382, 710613885, 289651104,
            631169418, 578971416, 632570701, 686899320, 67899396, 898967468, 643451678, 632759408,
            418671400, 104173983, 222665498, 772819888, 296525820, 22796746, 801384976, 453273678,
            818690974, 963923692, 611384702, 96891587, 476663231, 935389470, 60997992, 676459859,
            786983106, 125094819, 30957638, 252901786, 892100076, 532078131, 84125301, 420838483,
            668873611, 446829003, 933321773, 307943700, 813990252, 773136630, 724301274, 857658256,
            186541779, 994237792, 301505450, 106324363, 335451089, 174468131, 167601909, 285968056,
            701583366, 927541246, 963625036, 620641876, 643520528, 932542040, 434655178, 965859750,
            347350955, 334938674, 97861422, 536814156, 156493326, 583984562, 896874296, 902020052,
            960760663, 706545473, 36306036, 788111609, 134308461, 934172534, 239517401, 478150056,
            11410997, 95121159, 198963665, 590688615, 787460677, 210526208, 906884893, 245933273,
            145520637, 726958623, 603411374, 42991290, 719684323, 745662297, 271704743, 330975352,
            1046526867, 191306097, 554071243, 318271466, 989886875, 593796640, 650024147,
            642692866, 724166265, 142988918, 67668431, 327885054, 206902998, 1004616813, 76176614,
            1027816322, 468354606, 654409143, 110261296, 243996218, 928997606, 1066321247,
            502720680, 682025919, 378134469, 1062325365, 821920870, 1016728630, 406093915,
            158671281, 689689617, 405162901, 66492040, 949673841, 810823647, 851770015, 274680178,
            981514408, 170790803, 801552827, 480883660, 352001781, 1016035660, 733106638,
            394769165, 976081810, 706517458, 561723515, 457781495, 502013852, 634186604, 60167422,
            928089815, 300307908, 159986493, 469133546, 935937339, 545827240, 759725448,
            1065842576, 696160348, 731326990, 574658750, 1048934137, 904187181, 707517750,
            781707120, 773786631, 635511298, 63210596, 49125328, 499969127, 211324883, 870286429,
            751482468, 278888281, 786972974, 472954427, 1048527661, 381618772, 125085932,
            342384532, 795904912, 405914384, 624165685, 38004905, 895388437, 995161828, 398320105,
            607985894, 847701840, 121386520, 647618867, 572270248, 1012882042, 427528299,
            922506177, 455650735, 696360741, 535840004, 295246858, 354980137, 292042599, 372568479,
            226952334, 290519926, 401495194, 616489441, 247997594, 585487066, 1066055554, 66184830,
            305324505, 961655534, 1039503754, 364301302, 406550354, 656008627, 613307946,
            323711989, 8707650, 343333390, 931755431, 851604977, 167841643, 377446913, 162017764,
            776573419, 216661983, 774330551, 751741374, 671638275, 205894752, 31058122, 69115191,
            858232448, 943301574, 664728141, 521084658, 330183642, 665211109, 914326002, 802250210,
            228482658, 677927753, 333212096, 495275468, 713170499, 627390100, 365982564, 72260110,
            160696282, 727496087, 344938981, 892056784, 51426733, 183245418, 838077005, 202560421,
            57282652, 190821040, 1016971438, 575435483, 398432175, 794021028, 256289114, 52831309,
            85942479, 752501817, 172352490, 74596971, 660649186, 351278132, 517989357, 878653466,
            28492937, 440926287, 239904958, 394768467, 52692356, 87178073, 740582063, 119420282,
            500589932, 230153513, 255073504, 842031278, 840296980, 564865992, 892443468, 712337984,
            121638181, 763105035, 661976188, 727027863, 292673391, 80081396, 208142405, 538015866,
            1033635963, 416116139, 814848304, 149807576, 571152042, 380840922, 678980277,
            165072868, 359314187, 38778606, 363895620, 990169603, 1064320941, 750065115, 266510518,
            346886255, 774397217, 506859164, 885078484, 478558609, 299655818, 37280123, 904726422,
            210117464, 430873981, 532730175, 584036512, 989171333, 962174177, 835302333, 445309478,
            972109084, 24689598, 441958037, 351928454, 975978579, 120702508, 631222107, 719873027,
            763613542, 454804494, 915570503, 677883290, 14072569, 151298000, 103070031, 154157320,
            716604124, 80943885, 590144902, 62785281, 793207662, 373799524, 107979143, 129225737,
            324430071, 641468627, 707895452, 470036906, 257219313, 296877026, 510956851, 694907590,
            226542627, 122926065, 148106708, 354211464, 972925552, 210745068, 1010937523,
            421908684, 485710096, 880998896, 61524635, 462245822, 135002452, 927583762, 815438455,
            1010681881, 504259144, 790183054, 365119777, 1048557117, 1054544093, 166251122,
            890599827, 282020837, 566207930, 40814369, 453328627, 645631990, 195831343, 981405298,
            16238202, 335227283, 897771131, 565385541, 630088717, 838382965, 596170779, 1057068453,
            779308047, 6239781, 1029577433, 327520727, 64744918, 401897711, 731798728, 859663683,
            721051504, 411699290, 336737102, 618585778, 827085859, 748115794, 879529505, 458828134,
            258585828, 212400518, 914386371, 377610800, 1067040804, 648391949, 47843112, 365934390,
            421782391, 686240323, 328387727, 619073116, 258980248, 764287389, 688869338, 273927268,
        ],
    )
    .unwrap();
    let bb: ArrayView1<ufield> = ArrayView::from_shape(
        (32,),
        &[
            60531279, 467520031, 178724026, 491105913, 192757869, 325819833, 330086093, 574229647,
            154085544, 1013323197, 73847870, 392365210, 948594510, 811558141, 880173843, 873337552,
            1022944426, 965156743, 741515326, 1052796413, 693532363, 1039008995, 72774241,
            587347470, 113162756, 318623037, 1027891199, 625994145, 691088040, 484353051,
            946421517, 136099101,
        ],
    )
    .unwrap();
    let p: ufield = 1073741789;
    let p = &FastModulus::from(p);
    let x: ArrayView1<ufield> = ArrayView::from_shape(
        (32,),
        &[
            358669835, 78778428, 86102024, 469970933, 254210089, 675461243, 325224612, 789015738,
            1035476827, 452389121, 552870816, 193753118, 760141721, 361956077, 241467284,
            904111453, 566448215, 471587251, 397800758, 408209088, 295971958, 628065263, 67007390,
            792408688, 653740104, 610941238, 332434066, 613436094, 676775879, 929035710, 930236134,
            287989752,
        ],
    )
    .unwrap();
    b.iter(|| {
        let r = zp::solve(&a, &bb, p).unwrap();
        assert_eq!(r, x);
        r
    });
}
