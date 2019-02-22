/*IDEA.C   v2.2
	c source code for IDEA block cipher. IDEA (International Data
	Encryption Algorithm), formerly known as IPES (Improved Proposed
	Encryption Standard). Algorithm developed by Xuejia Lai and James L.
	Massey, of ETH Zurich. This implementation modified and derived from
	original C code developed by Xuejia Lai. Zero-based indexing added,
	names changed from IPES to IDEA. CFB functions added. Random Number
	routines added. Optimized for speed 21 Oct 92 by Colin Plumb
	<colin@nsq.gts.org>  This code assumes that each pair of 8-bit bytes
	comprising a 16-bit word in the key and in the cipher block are
	externally represented with the Most Significant Byte (MSB) first,
	regardless of internal native byte order of the target cpu.
	modified for use with PC files by Colin Maroney 4/1/94*/

/*   USAGE:     pass a key made up of 8 16-bit numbers (word16) in an array
		("word16 key[8];"), an input FILE * and an output temporary
		FILE * to either encode_file() or decode_file().
		where the key comes from is up to you.
		then call swap_files_and_clean_up() with the original file's
		name as the argument, to replace the original file
		with the encoded data (stored in the temporary file).

		you can remname the tempfile to be used in idea.h
		noisy is an integer which tells encrypting/decrypting
		functions to echo a "." every 256 writes, so the user can
		see that something is happening. set it to 0 for quiet
		running.

		please note that for really good security the original file
		is overwritten before being erased if you use the w switch.
		otherwise it outputs a file "<filename>.enc"

		the main() used here as illustration reads the filename
		from the command line arguments, as well as a command
		"e" or "d" to tell it whether to encrypt or
		decrypt, and a key.  the older versions had an interface
		for when a command line was not use.  lack of editing 
		features made this buggy, so i axed it. */


#include "idea.h"

void getuserkeyfromargv(word16 *key, char *arg);

uint16 inv(uint16 x)
{
    uint16 t0,t1;
    uint16 q,y;
    if (x<=1)
        return x;
    t1=(uint16)(0x10001l/x);
    y=(uint16)(0x10001l%x);
    if (y==1)
        return low16(1-t1);
    t0=1;
    do
    {
        q=x/y;
        x=x%y;
        t0+=q*t1;
        if (x==1)
            return t0;
        q=y/x;
        y=y%x;
        t1+=q*t0;
    } while (y!=1);
    return low16(1-t1);
}

void en_key_idea(word16 *userkey, word16 *Z)
{
    int i,j;
    /* shifts */
    for (j=0;j<8;j++)
        Z[j]=*userkey++;
    for (i=0;j<KEYLEN;j++)
    {
        i++;
        Z[i+7]=((Z[i&7] << 9) | (Z[i+1 & 7] >> 7));
        Z+=i&8;
        i&=7;
    }
}

void de_key_idea(IDEAkey Z,IDEAkey DK)
{
    int j;
    uint16 t1,t2,t3;
    IDEAkey T;
    word16 *p=T+KEYLEN;
    t1=inv(*Z++);
    t2=-*Z++;
    t3=-*Z++;
    *--p=inv(*Z++);
    *--p=t3;
    *--p=t2;
    *--p=t1;
    for (j=1;j<ROUNDS;j++)
    {
        t1=*Z++;
        *--p=*Z++;
        *--p=t1;
        t1=inv(*Z++);
        t2=-*Z++;
        t3=-*Z++;
        *--p=inv(*Z++);
        *--p=t2;
        *--p=t3;
        *--p=t1;
    }
    t1=*Z++;
    *--p=*Z++;
    *--p=t1;
    t1=inv(*Z++);
    t2=-*Z++;
    t3=-*Z++;
    *--p=inv(*Z++);
    *--p=t3;
    *--p=t2;
    *--p=t1;
    /*copy and destroy temp copy*/
    for(j=0,p=T;j<KEYLEN;j++)
    {
        *DK++=*p;
        *p++=0;
    }
}


uint16 mul(uint16 a, uint16 b)
{
    word32 p;

    if (a)
    {
        if (b)
        {
            p=(word32)a*b;
            b=(uint16)(low16(p));
            a=(uint16)(p>>16);
            return b-a+(b<a);
        }
        else
        {
            return 1-a;
        }
    }
    else
        return 1-b;
}

#define MUL(x,y) (x=mul(low16(x),y))


#define CONST

void cipher_idea(word16 in[4],word16 out[4],register CONST IDEAkey Z)
{
    register uint16 x1,x2,x3,x4,t1,t2;
    int r=ROUNDS;
    x1=*in++; x2=*in++;
    x3=*in++; x4=*in;
    do
    {
        MUL(x1,*Z++);
        x2+=*Z++;
        x3+=*Z++;
        MUL(x4,*Z++);
        t2=x1^x3;
        MUL(t2,*Z++);
        t1=t2+(x2^x4);
        MUL(t1,*Z++);
        t2=t1+t2;
        x1^=t1;
        x4^=t2;
        t2^=x2;
        x2=x3^t1;
        x3=t2;
    } while (--r);
    MUL(x1,*Z++);
    *out++=x1;
    *out++=(x3+*Z++);
    *out++=(x2+*Z++);
    MUL(x4,*Z);
    *out=x4;
}

char read_char_from_file(FILE *fp)
{
    char temp=0;

    if ((fread(&temp,sizeof(char),1,fp))!=1)
        end_of_file=1;

    return (temp);
}

word16 read_word16_from_file(FILE *fp)
{
    word16 temp=0;

    if ((fread(&temp,sizeof(word16),1,fp))!=1)
        end_of_file=1;

    return temp;
}

void write_char_to_file(char data,FILE *fp)
{
    if ((fwrite(&data,sizeof(char),1,fp))!=1)
    {
        printf("Fatal Error writing output file!!!\n");
        exit(-1);
    }
}

void write_word16_to_file(word16 data,FILE *fp)
{
    if ((fwrite(&data,sizeof(word16),1,fp))!=1)
    {
        printf("Fatal Error writing output file!!!\n");
        exit(-1);
    }
}

long filelength(FILE *fp) {
    fseek(fp, 0L, SEEK_END);
    long sz = ftell(fp);
    fseek(fp, 0L, SEEK_SET);
    return sz;
}


void cipher_file(FILE *in,FILE *out,word16 *key)
{
    word16 input[4],output[4];
    IDEAkey Z;
    int x,y;
    int count=0;
    uint32_t length;
    int temp;

    en_key_idea(key,Z);
    end_of_file=0;

    length = (uint32_t) filelength(in);
    fwrite(&length, sizeof(uint32_t),1,out);

    while (!end_of_file)
    {
        x=0;

        while (x<4)
        {
            input[x]=((word16)(read_char_from_file(in)<<8));
            if (!end_of_file)
            {
                temp=read_char_from_file(in);
                if (temp<0) temp+=256;
                input[x]=input[x]|temp;
                x++;
            }
            if (end_of_file)
            {
                while (x<4) input[x++]=0;
                break;
            }
        }

        cipher_idea(input,output,Z);

        for (y=0;y<x;y++)
        {
            if (noisy) if (count++%256==0) printf(".");
            write_word16_to_file(output[y],out);
        }
    }
}

void decipher_file(FILE *in,FILE *out,word16 *key)
{
    word16 input[4],output[4];
    int x;
    int y;
    IDEAkey Z;
    IDEAkey DK;
    int count = 0;
    int32_t length = 0;

    en_key_idea(key,Z);
    de_key_idea(Z,DK);

    end_of_file=0;

    fread(&length,sizeof(int32_t),1,in);

    while (!end_of_file)
    {
        x=0;
        while (x<4)
        {
            input[x]=read_word16_from_file(in);
            if (end_of_file)
                break;
            x++;
        }
        cipher_idea(input,output,DK);
        for (y=0;y<x;y++)
        {
            if (noisy) if (count++%256==0) printf(".");
            if (length-->0)
                write_char_to_file(((char)(output[y]>>8)),out);
            if (length-->0)
                write_char_to_file(((char)(output[y]&255)),out);
        }
    }
}


#define NUM_WORDLIST_LINES   2000000

int read_file(char *fname, char lines[NUM_WORDLIST_LINES][9]) {
    char *line = NULL;
    size_t len = 0;
    size_t read;
    FILE * fp;
    
    fp = fopen(fname, "r");
    if (fp == NULL)
        exit(EXIT_FAILURE);
    
    int i=0;
    while ((read = getline(&line, &len, fp)) != -1) {
        read--;
        // printf("Retrieved line of length %zu:\n", read);
        // printf("%s", line);
        // don't need null in lines, since it's zero'd
        strncpy(lines[i], line, read);
        i++;
        if (i == NUM_WORDLIST_LINES) {
            break;
        }
    }
    
    close(fp);
    
    return i;
}

char words[NUM_WORDLIST_LINES][8+1] = {0};


int crack_file(FILE *in, char* wordlist_fname)
{
    word16 input[4],output[4];
    int x;
    int y;
    IDEAkey Z;
    IDEAkey DK;
    int count = 0;
    int32_t length = 0;

    word16 key[8];

    end_of_file=0;

    fread(&length,sizeof(int32_t),1,in);

    x=0;
    while (x<4)
    {
        input[x]=read_word16_from_file(in);
        if (end_of_file)
            break;
        x++;
    }

    // char *words[] = {"apple1", "apple2", "apple", "apple3"}; 
    
    printf("reading file\n");
    int num_words = read_file(wordlist_fname, words);
    printf("done reading file - read %d words\n", num_words);
       
    for (int i=0; i < num_words; i++) {
        if (i%100000==0) {
            // printf(".");
            printf("trying %s\n", words[i]);
        }

        getuserkeyfromargv(key, words[i]);
        en_key_idea(key,Z);
        de_key_idea(Z,DK);
        cipher_idea(input,output,DK);
    
        /* test for zip file in the output */
        // printf("output[0]: %0x   output[1]: %0x\n", output[0], output[1]);
        if (output[0] == 0x504b && output[1] == 0x0304) {
            printf("it's a zip! - found password '%s'\n", words[i]);
            return 0;
        } else {
            // printf("not a zip\n");
            // return 1;
        }
    }
    return 1;
}



void swap_files_and_clean_up(char *file)
{
    long fsize,count;
    FILE *fp;
    char temp[100];

    if (overwrite)
    {
        if ((fp=fopen(file,"r+b"))==NULL)
        {
            printf("\nError overwriting old file, security compromised.\n");
        }
        else
        {
            fseek(fp,0l,SEEK_END);
            fsize=ftell(fp);
            fseek(fp,0l,SEEK_SET);
            for (count=0;count<fsize;count++)
                fputc('0',fp);
            fclose(fp);
        }

        if ((remove(file))!=0)
        {
            printf("\nERROR removing old file <%s>\n",file);
            printf("encoded data remains in temporary file <%s>\n",tempfilename);
            exit(-1);
        }
    }
    else
    {
        strcpy(temp,file);
        file=strtok(temp,".");
        strcat(file,".enc");
    }

    if ((rename(tempfilename,file))!=0)
    {
        printf("\nERROR renaming temporary file <%s>!!\n",tempfilename);
        printf("Data is safely processed and stored in that file.\n");
        exit(-1);
    }
}





/*-----------------------------------------------*/


#define KBYTES 1024

void getuserkeyfromargv(word16 *key, char *arg)
{
    int x;

    for (x=0;x<strlen(arg) && x<8;x++)
    {
        if (x==0) key[x]=arg[x]<<8;
        else key[x]=((arg[x]<<8)|(key[x-1]>>8));
    }

    /*
    if (strlen(arg)>8)
        printf ("\nONLY first *8* characters of key used!!!\n");
    */

    if (x<8) while (x<8) key[x++]=0;
}

int main(int argc, char **argv)
{
    word16 userkey[8];
    char filename[100];
    FILE *fp,*temp;
    int to_or_from;
    int crack = 0;

    noisy=1;
    overwrite=0;

    if (argc!=4)
    {
        printf("\nUsage: idea filename.ext [e|d[w]] key\n");
        printf("          e=encode   d=decode   w=overwrite file\n");
        printf("          c=crack  <wordlist-file>  - test for zip in result.\n");
        printf("       NOTE: Key must be no longer than 8 characters long!!!\n");
        exit(-1);
    }
    else
    {
        strncpy(filename,argv[1],99);
        filename[99]='\0';
        if (argv[2][0]=='e') to_or_from=1;
        else if (argv[2][0]=='d') to_or_from=0;
        else if (argv[2][0]=='c') crack=1;
        else
        {
            printf("\nUsage: idea filename.ext [e|d[w]] key\n");
            printf("		e=encrypt d=decrypt w=overwrite file\n");
            printf("		c=crack  <wordlist-file>  - test for zip in result.\n");
            printf("       NOTE: Key must be no longer than 8 characters long!!!\n");
            exit(-1);
        }
        if (argv[2][1]=='w') overwrite=1;
        getuserkeyfromargv(userkey,argv[3]);
    }


    if ((fp=fopen(filename,"r+b"))==NULL)
    {
        printf("\nError opening File %s\n",filename);
        exit (-1);
    }

    if ((temp=fopen(tempfilename,"w+b"))==NULL)
    {
        printf("\nError opening temporary file\n");
        exit(-1);
    }

    if (crack) {
        printf("cracking\n");
        exit(crack_file(fp, argv[3]));
        
    } else if (to_or_from==1)
    {
        printf("\nEncoding file %s   \n",filename);
        cipher_file(fp,temp,userkey);
    }
    else
    {
        printf("\nDecoding file %s   \n",filename);
        decipher_file(fp,temp,userkey);
    }

    fclose (fp);
    fclose(temp);

    swap_files_and_clean_up(filename);

    return 0;
}
