



























���ǱȽϽӽ�����ԭʼ�����һ���汾�����Ĵ��뾭����lost in the future��������fork��һ�ݡ�

����ķų����Ĵ��������в��˵ģ��������ﲹȫ��һЩ�����������ܹ����С�

��Щ��ȫ���Ǵ������ռ��ġ���ذ�Ȩ�Ķ����ڸ���ԭʼ������

�ĵ�������[����](https://github.com/spiritbear/Grad-School-Code)�����ݴ������Ʋ⣬���߿��ܵ�ʱ������ͬ�ࡣ

P423��Indiana��ѧ����ʱѡ�ı������Ŀγ̣�[����](https://github.com/srwaggon/p423)��[����](https://github.com/keyanzhang/p423-compiler)�����ҵ�һЩ�γ̵Ĵ��롣

�����в����ҷ����[���ĵ�����](http://zenlife.tk/nanopass0.md)��


# ����

[chez scheme](http://www.scheme.com/)��һ����ѵĽ������汾petite��ȥ�ҵ������ء�

    cd yscheme
    petite
    (load "compiler.ss")
    (test-one '(lambda (x) (+ x 1)))

���Կ������������

    generate-x86-64:
        .globl _scheme_entry
    _scheme_entry:
        pushq %rbx
        pushq %rbp
        pushq %r12
        pushq %r13
        pushq %r14
        pushq %r15
        movq %rdi, %rbp
        movq %rsi, %rdx
        leaq _scheme_exit(%rip), %r15
        movq %rdx, %rax
        addq $8, %rdx
        addq $2, %rax
        movq %rax, %rcx
        leaq L2(%rip), %rax
        movq %rax, -2(%rcx)
        movq %rcx, %rax
        jmp *%r15
    L2:
        movq %r9, %rax
        addq $8, %rax
        jmp *%r15
    _scheme_exit:
        popq %r15
        popq %r14
        popq %r13
        popq %r12
        popq %rbp
        popq %rbx
        ret

�Լ����Կ������п��Ե���test-one��������һЩ�����ǿ������õģ����磺

    (tracer #f) �ر��м���̵����
    (compiler-passes '(<spec> ...)) �������е�pass
    (test-one '<program>) ����һ�δ���

����Ŀ���ȥ��driver.ss�ļ�

-----------------------------------

# YScheme - an experimental compiler for Scheme


This is the final submission for a compiler course I took from <a
href="http://en.wikipedia.org/wiki/R._Kent_Dybvig">Kent Dybvig</a> at Indiana
University. The compiler compiles a significant subset of Scheme into X64
assembly and then links it with a runtime system written in C. I made attempts
to simplify and innovate the compiler, so it is quite different from Kent's
original design.

In Kent's words, I put myself into trouble each week by doing things differently
and then get myself out of it. Sometimes I did better than his compiler,
sometimes, worse. But eventually I passed all his tests and got an A+.

A notable thing of this compiler is its use of _high-order evaluation contexts_,
an advanced technique used in <a
href="https://github.com/yinwang0/lightsabers/blob/master/cps.ss">CPS
transformers</a>, which resulted sometimes in much simpler and shorter code.


### Copyright

Copyright (c) 2008-2014 Yin Wang, All rights reserved

Only the main compiler code is here. I don't have copyright of the rest of the
code (test framework, runtime system etc)


### References

For a history of the important compiler techniques contained in this compiler,
please refer to Kent's paper:

<a href="http://www.cs.indiana.edu/~dyb/pubs/hocs.pdf">The Development of Chez
Scheme</a>


For details of the compiler framework developed for the course, please refer to

<https://github.com/akeep/nanopass-framework>


For more information about CPS transformation, please refer to Andrew Appel's
book:

<a
href="http://www.amazon.com/Compiling-Continuations-Andrew-W-Appel/dp/052103311X">Compiling
with Continuations</a>

and Danvy and Filinski's paper

<a href="http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.46.84">Representing control: a study of the CPS transformation (1992)</a>


git :

echo "# 123" >> README.md
git init
git add README.md
git commit -m "first commit"
git remote add origin https://github.com/haskellstudio/scheme.git
git push -u origin master
��or push an existing repository from the command line
git remote add origin https://github.com/haskellstudio/scheme.git
git push -u origin master


git commit -m "msg"
git.exe fetch -v --progress "origin"
git.exe pull --progress -v --no-rebase "origin" master
git.exe push --progress "origin" master

git.exe clean -n  -d  -fx
git.exe clean -d  -fx
